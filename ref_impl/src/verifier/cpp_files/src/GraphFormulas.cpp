#include "GraphFormulas.h"

GraphFormulas::GraphFormulas(const char * smt_file) : 
  formulas(ctx.parse_file(smt_file)) {
    for(const auto formula : formulas){
      switch(formula.is_quantifier()){
        case false:
          break;
        case true:
          unsigned num_patterns = Z3_get_quantifier_num_patterns(ctx, formula);
          for(unsigned  pattern_index = 0;
              pattern_index < num_patterns;
              pattern_index++){
            auto pattern = z3::expr(ctx, 
                Z3_pattern_to_ast(ctx, 
                  Z3_get_quantifier_pattern_ast(ctx, formula, pattern_index)));
            // TODO: build the graph using the formula and pattern
            std::cout << pattern << std::endl;
          }
          break;
      }
    }
  } 

