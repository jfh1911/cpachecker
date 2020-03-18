// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.cpa.predicate;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ListMultimap;
import com.google.common.collect.MultimapBuilder;
import com.google.common.collect.Sets;
import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionStage;
import java.util.function.Consumer;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.IO;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.DummyCFAEdge;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression.BinaryOperator;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.AnalysisDirection;
import org.sosy_lab.cpachecker.core.Specification;
import org.sosy_lab.cpachecker.core.algorithm.bmc.candidateinvariants.CandidateInvariant;
import org.sosy_lab.cpachecker.core.algorithm.bmc.candidateinvariants.ExpressionTreeLocationInvariant;
import org.sosy_lab.cpachecker.core.interfaces.Statistics;
import org.sosy_lab.cpachecker.core.interfaces.StatisticsProvider;
import org.sosy_lab.cpachecker.core.specification.Specification;
import org.sosy_lab.cpachecker.cpa.automaton.AutomatonGraphmlParser;
import org.sosy_lab.cpachecker.cpa.predicate.persistence.PredicateMapParser;
import org.sosy_lab.cpachecker.cpa.predicate.persistence.PredicatePersistenceUtils.PredicateParsingFailedException;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.WitnessInvariantsExtractor;
import org.sosy_lab.cpachecker.util.expressions.ExpressionTree;
import org.sosy_lab.cpachecker.util.expressions.LeafExpression;
import org.sosy_lab.cpachecker.util.predicates.AbstractionManager;
import org.sosy_lab.cpachecker.util.predicates.AbstractionPredicate;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap;
import org.sosy_lab.cpachecker.util.predicates.pathformula.ctoformula.CtoFormulaConverter;
import org.sosy_lab.cpachecker.util.predicates.pathformula.ctoformula.CtoFormulaTypeHandler;
import org.sosy_lab.cpachecker.util.predicates.pathformula.ctoformula.FormulaEncodingOptions;
import org.sosy_lab.cpachecker.util.predicates.precisionConverter.Converter.PrecisionConverter;
import org.sosy_lab.cpachecker.util.predicates.smt.FormulaManagerView;
import org.sosy_lab.cpachecker.util.statistics.KeyValueStatistics;
import org.sosy_lab.java_smt.api.BooleanFormula;

@Options(prefix = "cpa.predicate")
public class PredicatePrecisionBootstrapper implements StatisticsProvider {

  @Option(
    secure = true,
    name = "abstraction.initialPredicates",
    description = "get an initial map of predicates from a list of files (see source doc/examples/predmap.txt for an example)")
  @FileOption(FileOption.Type.OPTIONAL_INPUT_FILE)
  private List<Path> predicatesFiles = ImmutableList.of();

  @Option(
    secure = true,
    description = "always check satisfiability at end of block, even if precision is empty")
  private boolean checkBlockFeasibility = false;

  @Options(prefix = "cpa.predicate.abstraction.initialPredicates")
  public static class InitialPredicatesOptions {

    @Option(
      secure = true,
      description = "Apply location-specific predicates to all locations in their function")
    private boolean applyFunctionWide = false;

    @Option(
      secure = true,
      description = "Apply location- and function-specific predicates globally (to all locations in the program)")
    private boolean applyGlobally = false;

    @Option(
      secure = true,
      description = "when reading predicates from file, convert them from Integer- to BV-theory or reverse.")
    private PrecisionConverter encodePredicates = PrecisionConverter.DISABLE;

    @Option(secure = true, description = "initial predicates are added as atomic predicates")
    private boolean splitIntoAtoms = false;

    @Option(
      secure = true,
      description = "initial predicates are splitt into clauses, if they are a conmjunction")
    private boolean splittConjunctionsIntoClauses = false;

    public boolean applyFunctionWide() {
      return applyFunctionWide;
    }

    public boolean applyGlobally() {
      return applyGlobally;
    }

    public PrecisionConverter getPrecisionConverter() {
      return encodePredicates;
    }

  }

  private final FormulaManagerView formulaManagerView;
  private final AbstractionManager abstractionManager;

  private final Configuration config;
  private final LogManager logger;
  private final CFA cfa;

  private final Specification specification;
  private final ShutdownNotifier shutdownNotifier;
  private final PathFormulaManager pathFormulaManager;
  private final PredicateAbstractionManager predicateAbstractionManager;

  private final KeyValueStatistics statistics = new KeyValueStatistics();

  private final InitialPredicatesOptions options;

  public PredicatePrecisionBootstrapper(
      Configuration config,
      LogManager logger,
      CFA cfa,
      AbstractionManager abstractionManager,
      FormulaManagerView formulaManagerView,
      Specification specification,
      ShutdownNotifier shutdownNotifier,
      PathFormulaManager pathFormulaManager,
      PredicateAbstractionManager predicateAbstractionManager)
      throws InvalidConfigurationException {
    this.config = config;
    this.logger = logger;
    this.cfa = cfa;

    this.abstractionManager = abstractionManager;
    this.formulaManagerView = formulaManagerView;

    this.specification = specification;
    this.shutdownNotifier = shutdownNotifier;
    this.pathFormulaManager = pathFormulaManager;
    this.predicateAbstractionManager = predicateAbstractionManager;

    config.inject(this);

    this.options = new InitialPredicatesOptions();
    config.inject(this.options);
  }

  private PredicatePrecision internalPrepareInitialPredicates()
      throws InvalidConfigurationException, InterruptedException {

    PredicatePrecision result = PredicatePrecision.empty();

    if (checkBlockFeasibility) {
      result =
          result
              .addGlobalPredicates(Collections.singleton(abstractionManager.makeFalsePredicate()));
    }

    // FIXME: Move to different location
    // if (predicatesFiles.isEmpty()) {
    // List<Path> preds = new ArrayList<>();
    // predicatesFiles = preds;
    // try {
    // List<Supplier<Path>> suppliers = new ArrayList<>();
    //
    // // Add all specified invariant generation tools
    //
    // ExternalInvariantGenerator gen =
    // ExternalInvariantGenerator.getInstance(ExternalInvariantGenerators.VERIABS, config);
    // suppliers.add(
    // gen.getSupplierGeneratingInvariants(
    // cfa,
    // new ArrayList<CFANode>(),
    // specification,
    // logger,
    // shutdownNotifier,
    // config));
    //
    // // Start the computation
    // List<CompletableFuture<Path>> generatedInvariants =
    // suppliers.parallelStream()
    // .map(s -> CompletableFuture.supplyAsync(s))
    // .collect(Collectors.toList());
    // CompletableFuture<Path> c = anyOf(generatedInvariants);
    //
    // try {
    // predicatesFiles.add(c.get());
    // } catch (InterruptedException | ExecutionException e) {
    // logger.log(
    // Level.WARNING,
    // "The invariant generation was interruped. Continue without additional invariant.");
    // e.printStackTrace();
    // }
    // // FIXME: just for tests: print the generated invariant
    // BufferedReader reader;
    // try {
    // String fileContent = "";
    // reader = Files.newBufferedReader(predicatesFiles.get(0), Charset.defaultCharset());
    // String line;
    // while ((line = reader.readLine()) != null) {
    // fileContent = fileContent.concat(line);
    // }
    // reader.close();
    //
    // logger.log(Level.WARNING, fileContent);
    // } catch (IOException e) {
    // logger.log(Level.WARNING, "Cannot print the file");
    // }
    //
    // } catch (CPAException e) {
    // // FIXME: This is only for the first evaluation!!
    // // throw new IllegalStateException(
    // // "The invariant generation via seahorn failed, due to " + e,
    // // e);
    // throw new IllegalArgumentException(e);
    // }
    // }

    if (!predicatesFiles.isEmpty()) {
      PredicateMapParser parser =
          new PredicateMapParser(cfa, logger, formulaManagerView, abstractionManager, options);

      for (Path predicatesFile : predicatesFiles) {
        try {
          IO.checkReadableFile(predicatesFile);
          if (AutomatonGraphmlParser.isGraphmlAutomatonFromConfiguration(predicatesFile)) {
            switch (AutomatonGraphmlParser.getWitnessType(predicatesFile)) {
              case CORRECTNESS_WITNESS:
                result =
                    result.mergeWith(
                        parseInvariantsFromCorrectnessWitnessAsPredicates(predicatesFile));
                break;
              case VIOLATION_WITNESS:
                logger.log(Level.WARNING, "Invariants do not exist in a violaton witness");
                break;
            }
          } else {
            result = result.mergeWith(parser.parsePredicates(predicatesFile));
          }

        } catch (IOException e) {
          logger.logUserException(Level.WARNING, e, "Could not read predicate precision from file");

        } catch (PredicateParsingFailedException e) {
          logger.logUserException(Level.WARNING, e, "Could not read predicate map");
        }
      }
    }
    // TODO: Find a more efficient way / only for test
    // if (result.getLocalPredicates()
    // .values()
    // .parallelStream()
    // .allMatch(
    // pred -> pred.getSymbolicAtom().toString().equals("`true`")
    // && pred.getAbstractVariable().toString().equals("`true`"))) {
    // throw new IllegalArgumentException(
    // "The witness is not read / parsed correctly, only true present");
    // } else {
    logger.log(Level.WARNING, "generated invarinats are:");
    result.getLocalPredicates()
        .values()
        .parallelStream()
        .forEach(pred -> logger.log(Level.WARNING, pred.toString()));
    // }
    return result;
  }

  @SuppressWarnings("rawtypes")
  private PredicatePrecision parseInvariantsFromCorrectnessWitnessAsPredicates(Path pWitnessFile) {
    PredicatePrecision result = PredicatePrecision.empty();
    try {
      final Set<ExpressionTreeLocationInvariant> invariants = Sets.newLinkedHashSet();
      WitnessInvariantsExtractor extractor =
          new WitnessInvariantsExtractor(
              config,
              specification,
              logger,
              cfa,
              shutdownNotifier,
              pWitnessFile);
      extractor.extractInvariantsFromReachedSet(invariants);

      for (ExpressionTreeLocationInvariant invariant : invariants) {

        ListMultimap<CFANode, AbstractionPredicate> localPredicates =
            MultimapBuilder.treeKeys().arrayListValues().build();
        Set<AbstractionPredicate> globalPredicates = Sets.newHashSet();
        ListMultimap<String, AbstractionPredicate> functionPredicates =
            MultimapBuilder.treeKeys().arrayListValues().build();

        List<AbstractionPredicate> predicates = new ArrayList<>();

        if (options.splittConjunctionsIntoClauses) {

        ExpressionTree tree = invariant.asExpressionTree();
        if (tree instanceof LeafExpression) {
          if (((LeafExpression) tree).getExpression() instanceof CExpression) {
            for (CExpression expr : splittIntoClauses(
                (CExpression) ((LeafExpression) tree).getExpression())) {

              CtoFormulaConverter conv =
                  new CtoFormulaConverter(
                      new FormulaEncodingOptions(config),
                      formulaManagerView,
                      cfa.getMachineModel(),
                      Optional.empty(),
                      logger,
                      shutdownNotifier,
                      new CtoFormulaTypeHandler(logger, cfa.getMachineModel()),
                      AnalysisDirection.FORWARD);
              // PathFormula pFormula = pathFormulaManager.makeEmptyPathFormula();

              CFAEdge edge = new DummyCFAEdge(null, null);
              String function = invariant.getLocation().getFunctionName();
              BooleanFormula f =
                  conv.makePredicate(expr, edge, function, SSAMap.emptySSAMap().builder());
                predicates
                    .add(abstractionManager.makePredicate(formulaManagerView.uninstantiate(f)));
            }
          }
        }
        } else {
        // get atom predicates from invariant
          if (options.splitIntoAtoms) {
          predicates.addAll(
              predicateAbstractionManager.getPredicatesForAtomsOf(
                  invariant.getFormula(formulaManagerView, pathFormulaManager, null)));

        }
        // get predicate from invariant
        else {
          predicates.add(
              abstractionManager.makePredicate(
                  invariant.getFormula(formulaManagerView, pathFormulaManager, null)));
          }
        }
        for (AbstractionPredicate predicate : predicates) {
          localPredicates.put(invariant.getLocation(), predicate);
          globalPredicates.add(predicate);
          functionPredicates.put(invariant.getLocation().getFunctionName(), predicate);
        }

        // add predicates according to the scope
        // location scope is chosen if neither function or global scope is specified or both are
        // specified which would be a conflict here
        boolean applyLocally =
            (!options.applyFunctionWide && !options.applyGlobally)
                || (options.applyFunctionWide && options.applyGlobally);
        if (applyLocally) {
          result = result.addLocalPredicates(localPredicates.entries());
        } else if (options.applyFunctionWide) {
          result = result.addFunctionPredicates(functionPredicates.entries());
        } else if (options.applyGlobally) {
          result = result.addGlobalPredicates(globalPredicates);
        }
      }
    } catch (CPAException | InterruptedException | InvalidConfigurationException e) {
      logger.logUserException(
          Level.WARNING,
          e,
          "Predicate from correctness witness invariants could not be computed");
    }
    return result;
  }

  private Collection<CExpression> splittIntoClauses(CExpression pExpression) {
    HashSet<CExpression> result = new HashSet<>();
    if (pExpression instanceof CBinaryExpression) {
      CBinaryExpression bin = (CBinaryExpression) pExpression;
      if (bin.getOperator()
          .equals(BinaryOperator.BINARY_AND)) {
        result.addAll(splittIntoClauses(bin.getOperand1()));
        result.addAll(splittIntoClauses(bin.getOperand2()));
      } else {
        result.add(bin);
      }
    } else {
      result.add(pExpression);
    }
    return result;
  }

  /** Read the (initial) precision (predicates to track) from a file. */
  public PredicatePrecision prepareInitialPredicates()
      throws InvalidConfigurationException, InterruptedException {
    PredicatePrecision result = internalPrepareInitialPredicates();

    statistics.addKeyValueStatistic("Init. global predicates", result.getGlobalPredicates().size());
    statistics
        .addKeyValueStatistic("Init. location predicates", result.getLocalPredicates().size());
    statistics
        .addKeyValueStatistic("Init. function predicates", result.getFunctionPredicates().size());

    return result;
  }

  @Override
  public void collectStatistics(Collection<Statistics> pStatsCollection) {
    pStatsCollection.add(statistics);
  }

  public static <T> CompletableFuture<T> anyOf(List<? extends CompletionStage<? extends T>> l) {

    // Code is taken from
    // https://stackoverflow.com/questions/33913193/completablefuture-waiting-for-first-one-normally-return
    CompletableFuture<T> f = new CompletableFuture<>();
    Consumer<T> complete = f::complete;
    CompletableFuture
        .allOf(l.stream().map(s -> s.thenAccept(complete)).toArray(CompletableFuture<?>[]::new))
        .exceptionally(ex -> {
          f.completeExceptionally(ex);
          return null;
        });
    return f;
  }

}
