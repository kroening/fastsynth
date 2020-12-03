#include <set>

#include <solvers/smt2/smt2_tokenizer.h>

#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>

class sygus_parsert
{
public:
  explicit sygus_parsert(std::istream &_in):
    id_counter(0),
    let_counter(0),
    smt2_tokenizer(_in)
  {
  }

  using smt2_errort = smt2_tokenizert::smt2_errort;

  smt2_tokenizert::smt2_errort error(const std::string &message)
  {
    return smt2_tokenizer.error(message);
  }

  smt2_tokenizert::smt2_errort error()
  {
    return smt2_tokenizer.error();
  }

  void parse()
  {
    command_sequence();
  }

  enum invariant_variablet { PRIMED, UNPRIMED };
  enum invariant_constraint_functiont { PRE, INV, TRANS, POST };

  struct signature_with_parameter_idst
  {
    mathematical_function_typet type;
    std::vector<irep_idt> parameter_ids;

    signature_with_parameter_idst(
      const mathematical_function_typet &_type,
      const std::vector<irep_idt> &_parameter_ids):
      type(_type), parameter_ids(_parameter_ids)
    {
    }
  };

  exprt::operandst constraints;
  std::string logic, action;

  std::set<irep_idt> synth_fun_set;

  signature_with_parameter_idst inv_function_signature();
  void expand_function_applications(exprt &);
  void generate_invariant_constraints();

  function_application_exprt apply_function_to_variables(
    invariant_constraint_functiont id,
    invariant_variablet variable_use);

  struct functiont
  {
    mathematical_function_typet type;
    std::vector<irep_idt> parameter_ids;
    exprt body;
    functiont():type({}, empty_typet())
    {
    }
  };

  using function_mapt=std::map<irep_idt, functiont>;
  function_mapt function_map;

  using variable_mapt=std::map<irep_idt, typet>;

  variable_mapt variable_map;
  variable_mapt local_variable_map;
  variable_mapt let_variable_map;
  variable_mapt full_let_variable_map;

  unsigned id_counter;
  unsigned let_counter;
  using renaming_mapt=std::map<irep_idt, irep_idt>;
  renaming_mapt renaming_map;

protected:
  smt2_tokenizert smt2_tokenizer;

  void command_sequence();

  virtual void command(const std::string &);

  void ignore_command();

  exprt expression();
  exprt let_expression(bool first_in_chain);
  typet sort();
  exprt::operandst operands();
  signature_with_parameter_idst function_signature();
  exprt function_application(const irep_idt &identifier, const exprt::operandst &op);
  void fix_binary_operation_operand_types(exprt &expr);
  void fix_ite_operation_result_type(if_exprt &expr);
  exprt cast_bv_to_signed(exprt &expr);
  exprt cast_bv_to_unsigned(exprt &expr);
  void check_bitvector_operands(exprt &expr);

  /// Helper to consume and ignore SyGuS V2 grammars.
  void NTDef_seq();
  void GTerm_seq();
  void NTDef();
  void GTerm();
};

