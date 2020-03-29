#ifndef _GRAPH_FORMULAS
#define _GRAPH_FORMULAS

#include <iostream>
#include <z3++.h>

class GraphFormulas {
  z3::context ctx;
  z3::expr_vector formulas;
  public:
    GraphFormulas(const char *);
};

#endif
