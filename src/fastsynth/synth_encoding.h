#include <util/std_expr.h>

struct e_datat
{
public:
  e_datat():setup_done(false) { }

  struct instructiont
  {
    explicit instructiont(std::size_t _pc):pc(_pc)
    {
    }

    std::size_t pc;

    // constant
    symbol_exprt constant_sel;
    symbol_exprt constant_val;

    // parameter
    std::vector<symbol_exprt> parameter_sel;
    
    // result of the instruction
    // for a set of arguments
    exprt result(const std::vector<exprt> &arguments);
  };

  std::vector<instructiont> instructions;

  // result of the function application
  // for a set of arguments
  exprt result(const std::vector<exprt> &arguments);

  void setup(const function_application_exprt &);
  std::vector<typet> parameter_types;
  symbol_exprt function_symbol;

protected:
  bool setup_done;
};

