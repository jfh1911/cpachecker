# name for the executable file
EXE := prepare_c_file_for_seahorn

# important special files
MAIN_FILE := prepare_c_file_for_seahorn.cpp

# compiler to use
CXX := clang++

# compiler flags
CXX_FLAGS := -std=c++14
CXX_FLAGS += -Wall
CXX_FLAGS += -Wextra
CXX_FLAGS += -O0
# CXX_FLAGS += -march=native
# CXX_FLAGS += -DNDEBUG
CXX_FLAGS += -pipe
CXX_FLAGS += -g
CXX_FLAGS += -rdynamic



# definition of targets
.PHONY: clean

all:
	$(CXX) $(CXX_FLAGS)  $(MAIN_FILE)  $(LIBS) -o $(EXE)

clean:
	rm -f $(EXE)
