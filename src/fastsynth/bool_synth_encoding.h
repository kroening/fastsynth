/*******************************************************************\

 Module: Fastsynth Boolean Synth Encoding

 Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

#ifndef CPROVER_FASTSYNTH_BOOL_SYNTH_ENCODING_H
#define CPROVER_FASTSYNTH_BOOL_SYNTH_ENCODING_H

#include "synth_encoding_base.h"

#include <util/mathematical_expr.h>

#include <solvers/decision_procedure.h>

#include <set>

/// Data structure for holding the encoding of a synthesised expression.
class bool_e_datat
{
public:
  /// Type for the arguments of the synthesised expression.
  using argumentst = function_application_exprt::argumentst;

  /// Type for the generated list of constraints.
  using constraintst = std::list<exprt>;

  /// Type for associating arguments with instances.
  using instancest = std::map<argumentst, std::size_t>;

  /// Data structure for a single instruction of the synthesised expression.
  /// Includes options for a certain program size and is able to generate
  /// constraints for them.
  struct instructiont
  {
    /// Data structure for a possible option. Includes information about the
    /// operands, their relation, the type and the operation itself.
    struct optiont
    {
      /// Generates a new option with default values.
      optiont();

      /// Symbol specifying the selector. This is used to enable or disable
      /// certain options (Important when chaining multiple instructions).
      symbol_exprt sel = symbol_exprt::typeless(ID_empty_string);

      /// ID of the operation that this option models.
      irep_idt operation;

      /// The category of operation that is modelled by this option.
      enum
      {
        NONE,
        NULLARY,
        UNARY,
      } kind;

      /// Used to identify the operands for unary instructions.
      std::size_t operand;
    };
    using optionst = std::vector<optiont>;

    /// Program size for this instruction.
    std::size_t pc;

    /// Possible candidates for this instruction.
    optionst options;

    /// Creates a new instruction.
    /// \param pc: Current program size.
    explicit instructiont(std::size_t pc);

    /// Creates an option with the specified identifier and returns a reference
    /// to it to the caller.
    /// \param sel_identifier: Name of the option.
    /// \return: Reference to the newly created option.
    optiont &add_option(const irep_idt &sel_identifier);

    /// Generate a constraint for the instruction for a given set of arguments.
    /// This happens by concatenating the instruction with a previously
    /// generated constraint for another instruction.
    /// \param arguments: Arguments of the function.
    /// \param prev_result: Result of the previous instruction (Nil if there is
    ///   none).
    /// \return: Result of the chaining process.
    exprt constraint(const argumentst &arguments, const exprt &prev_result);
  };

  /// List of constraints for the synthesised expression generated during the
  /// chaining process.
  constraintst constraints;

  /// Pre-configured constants to include in the expression set.
  std::set<constant_exprt> literals;

  /// Generates a new instance of this class. Sets up possible candidates for
  /// the given function by analysing the types of its parameters and building
  /// fitting options.
  /// \param expression: Expression to find candidates for.
  /// \param program_size: The maximum number of allowed operands.
  bool_e_datat(
    const function_application_exprt &expression,
    const std::size_t program_size);

  /// Computes the constraints for the given arguments with respect to the
  /// generated options by chaining them together.
  /// \param arguments: Arguments of the function that shall be synthesised.
  /// \return: Encoded result.
  exprt operator()(const argumentst &arguments);

  /// Returns one possible decoded result for the synthesised expression. This
  /// is based on the previously generated instructions.
  /// \param solver: Solver used by the synthesis, used for retrieving which
  ///   selectors are active.
  /// \return: Possible solution for the synthesised expression.
  exprt get_function(const decision_proceduret &solver) const;

  /// Checks if all parameters of the expression are of type bool.
  /// \return False if there is a parameter of a type other than bool, true
  ///   otherwise.
  bool is_bool_word_type();

  /// Returns the instance number for a given set of arguments and adds a new
  /// instance entry if not already present.
  /// \param arguments: Arguments to perform the search for.
  /// \return: Number of the instance.
  std::size_t instance_number(const argumentst &arguments);

private:
  /// All instructions of the data structure.
  std::vector<instructiont> instructions;

  /// Symbol of the synthesised expression to which this bool_e_data belongs.
  symbol_exprt function_symbol = symbol_exprt::typeless(ID_empty_string);

  /// Arguments of the synthesised expression to which this bool_e_data
  /// belongs.
  const argumentst function_arguments;

  /// Data structure for associating arguments with instances.
  instancest instances;

  /// Removes literals from the structure if they do not fit the current word
  /// type.
  void erase_unfitting_literals();

  /// Constructs an unary expression for the given option.
  /// \param option: Option to create the expression for.
  /// \param rlo_bit: Current state of the RLO. Can be interpreted as the
  /// intermediate result of the boolean operation.
  /// \return: New RLO expression.
  exprt decode_unary(
    const bool_e_datat::instructiont::optiont &option,
    const exprt &rlo_bit) const;

  /// Constructs a nullary expression for the given option.
  /// \param option: Option to create the expression for.
  /// \param rlo_bit: Current state of the RLO. Can be interpreted as the
  /// intermediate result of the boolean operation.
  /// \return: New RLO expression.
  exprt decode_nullary(
    const bool_e_datat::instructiont::optiont &option,
    const exprt &rlo_bit) const;

  /// Constructs a parameter for the given parameter number.
  /// \param parameter_number: Number of the synthesised expression's
  ///   parameter.
  /// \return: Expression containing the parameter.
  symbol_exprt decode_parameter(const size_t parameter_number) const;
};

/// Responsible for providing an encoding for the synthesis of boolean
/// functions.
class bool_synth_encodingt : public synth_encoding_baset
{
public:
  /// Performs the encoding for the given expression by setting up possible
  /// candidates and computing constraints for them.
  /// \param expr: Expression that shall be encoded.
  /// \return: Encoded result.
  exprt operator()(const exprt &expr) override;

  /// Returns a set of solutions based on the encoded possibilities.
  /// \param solver: Solver used by the synthesis.
  /// \return: Solution including possible candidates for the final result.
  solutiont get_solution(const decision_proceduret &solver) const override;

  /// Clears the encoded variants and constraints.
  void clear() override;

protected:
  /// Association between functions to synthesise and their corresponding
  /// encodings.
  std::map<symbol_exprt, bool_e_datat> e_data_per_function;
};

#endif /* CPROVER_FASTSYNTH_BOOL_SYNTH_ENCODING_H */
