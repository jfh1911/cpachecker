/*******************************************************************************
 * Copyright (c) 2000, 2008 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.sosy_lab.cpachecker.plugin.eclipse.wizards;

import java.io.IOException;
import java.util.Collections;

import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchWizard;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.cpachecker.plugin.eclipse.CPAcheckerPlugin;
import org.sosy_lab.cpachecker.plugin.eclipse.TaskRunner;
import org.sosy_lab.cpachecker.plugin.eclipse.TaskRunner.Task;


public class NewTaskCreationWizard extends Wizard implements IWorkbenchWizard{
	private NewTaskCreationWizardPage firstPage;
	private IWorkbench workbench;
	private IStructuredSelection selection;
	
	public NewTaskCreationWizard() {
		super();
		firstPage = new NewTaskCreationWizardPage("First Page", this);
		addPage(firstPage);
	}

	@Override
	public boolean performFinish() {
		System.out.println("Config: " + firstPage.getConfigText());
		System.out.println("Source: " + firstPage.getSourceText());
		
		Task t = new TaskRunner.Task("defaultName", firstPage.getConfigText(), firstPage.getSourceText());
		CPAcheckerPlugin.getPlugin().addTask(t);
		return true;
	}
	
	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		this.workbench = workbench;
		this.selection = selection;
		setWindowTitle("neuer Task");
		//setDefaultPageImageDescriptor(ReadmeImages.README_WIZARD_BANNER);
	}
}
