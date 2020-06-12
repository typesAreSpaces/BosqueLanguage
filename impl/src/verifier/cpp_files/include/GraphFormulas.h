#ifndef _GRAPH_FORMULAS
#define _GRAPH_FORMULAS

#include <iostream>
#include <vector>
#include <list>
#include <z3++.h>

class GraphFormulas {
  z3::context ctx;
  z3::expr_vector assertions;
  public:
    GraphFormulas(const char *);
    friend std::ostream & operator << (std::ostream &, const GraphFormulas &);
};

#endif
