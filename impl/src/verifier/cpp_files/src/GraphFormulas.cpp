#include "GraphFormulas.h"

GraphFormulas::GraphFormulas(const char * smt_file) : 
  assertions(ctx.parse_file(smt_file))
{

  for(auto const & assertion : assertions){
    //std::cout << assertion << std::endl;
    //if(assertion.is_quantifier()){
      //unsigned num_patterns = Z3_get_quantifier_num_patterns(ctx, assertion);
      //for(unsigned  pattern_index = 0;
          //pattern_index < num_patterns;
          //pattern_index++){
        //auto pattern = z3::expr(ctx, 
            //Z3_pattern_to_ast(ctx, 
              //Z3_get_quantifier_pattern_ast(ctx, assertion, pattern_index)));
        //// TODO: build the graph using the assertion and pattern
        //std::cout << pattern << std::endl;
      //}
    //}
  }
} 

std::ostream & operator << (std::ostream & os, const GraphFormulas & gfs) {
  return os;
}  
