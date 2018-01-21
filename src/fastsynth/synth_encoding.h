#ifndef CPROVER_FASTSYNTH_SYNTH_ENCODING_H_
#define CPROVER_FASTSYNTH_SYNTH_ENCODING_H_

#include <util/std_expr.h>
#include <util/decision_procedure.h>

struct e_datat
{
public:
  e_datat():setup_done(false) { }

  exprt operator()(
    const function_application_exprt &expr,
    const std::size_t program_size)
  {
    setup(expr, program_size);
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

    struct optiont
    {
      optiont():parameter_number(0), kind(NONE),
        operand0(0), operand1(0), operand2(0)
      {
      }

      symbol_exprt sel;
      irep_idt operation;
      std::size_t parameter_number;
      enum { NONE, PARAMETER, UNARY, BINARY, BINARY_PREDICATE, ITE } kind;
      std::size_t operand0, operand1, operand2;
      exprt type;
    };

    using optionst=std::vector<optiont>;
    optionst options;

    optiont &add_option(const irep_idt &sel_identifier)
    {
      options.push_back(optiont());
      options.back().sel=symbol_exprt(sel_identifier, bool_typet());
      return options.back();
    }

    // generate a constraint for the instruction
    // - for a given word type
    // - for a set of arguments
    // - for a given vector of previous results
    exprt constraint(
      const typet &word_type,
      const std::vector<exprt> &arguments,
      const std::vector<exprt> &results);

  protected:
    if_exprt chain(
      const symbol_exprt &selector,
      const exprt &,
      const exprt &);
  };

  std::vector<instructiont> instructions;

  // result of the function application
  // for a set of arguments

  symbol_exprt function_symbol;
  std::vector<typet> parameter_types;
  typet return_type;
  typet word_type;

  exprt get_expression(const decision_proceduret &) const;

  using constraintst=std::list<exprt>;
  constraintst constraints;

  typet compute_word_type();

  using instancest=
    std::map<function_application_exprt::argumentst, std::size_t>;
  instancest instances;

  using argumentst=
    function_application_exprt::argumentst;

  std::size_t instance_number(const argumentst &);

protected:
  bool setup_done;

  exprt result(const argumentst &);

  void setup(
    const function_application_exprt &,
    const std::size_t program_size);
};

class synth_encodingt
{
public:
  synth_encodingt():program_size(1) { }

  /// Virtual destructor for defined behaviour.
  virtual ~synth_encodingt() { }

  virtual exprt operator()(const exprt &);

  virtual std::map<symbol_exprt, exprt> get_expressions(
    const decision_proceduret &solver) const;

  std::string suffix;
  std::size_t program_size;

  using constraintst=std::list<exprt>;
  constraintst constraints;

protected:
  std::map<symbol_exprt, e_datat> e_data_map;
};

#endif /* CPROVER_FASTSYNTH_SYNTH_ENCODING_H_ */
