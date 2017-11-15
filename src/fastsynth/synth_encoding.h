#include <util/std_expr.h>
#include <util/decision_procedure.h>

struct e_datat
{
public:
  e_datat():setup_done(false) { }

  exprt operator()(const function_application_exprt &expr)
  {
    setup(expr);
    return result(expr.arguments());
  }

  struct instructiont
  {
    explicit instructiont(std::size_t _pc):pc(_pc)
    {
    }

    std::size_t pc;

    // constant, always the last resort
    symbol_exprt constant_val;

    // parameter
    std::vector<symbol_exprt> parameter_sel;

    // binary operation
    struct binary_opt
    {
      symbol_exprt sel;
      irep_idt operation;
      std::size_t operand0, operand1;
    };

    std::vector<binary_opt> binary_ops;

    binary_opt &add_binary_op()
    {
      binary_ops.push_back(binary_opt());
      return binary_ops.back();
    }
    
    // result of the instruction
    // - for a set of arguments
    // - for a given vector of previous results
    exprt result(
      const std::vector<exprt> &arguments,
      const std::vector<exprt> &results);
  };

  std::vector<instructiont> instructions;

  // result of the function application
  // for a set of arguments
  std::vector<typet> parameter_types;
  symbol_exprt function_symbol;

  exprt get_expression(const decision_proceduret &) const;

protected:
  bool setup_done;

  exprt result(const std::vector<exprt> &arguments);
  void setup(const function_application_exprt &);
};

class synth_encodingt
{
public:
  exprt operator()(const exprt &);

  exprt get_expression(
    const symbol_exprt &function_symbol,
    const decision_proceduret &solver) const;

  std::map<symbol_exprt, exprt> get_expressions(
    const decision_proceduret &solver) const;

  std::string suffix;

protected:
  std::map<symbol_exprt, e_datat> e_data_map;
};

