Z3DIR = /home/jose/Documents/GithubProjects/z3
Z3EXT = so

IDIR=./include
ODIR=./obj
SDIR=./src
CC=g++
FLAGS=-I$(SDIR) -I$(IDIR) -std=c++11 -Wall
PROJECT=terminator

SRC=$(wildcard $(SDIR)/*.cpp)
OBJS=$(patsubst $(SDIR)/%.cpp, $(ODIR)/%.o, $(SRC))
DEPS=$(wildcard $(IDIR)/*.h)

all: $(PROJECT) 

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -g -c -o $@ $(FLAGS) $<

$(PROJECT): $(OBJS) $(Z3DIR)/build/libz3.$(Z3EXT)
	$(CC) -g -o $@ $^ -lpthread

run: $(PROJECT) 
	./$(PROJECT)

.PHONY: clean
clean: 
	rm -rf $(ODIR)/* $(PROJECT)

