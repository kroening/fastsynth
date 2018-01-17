#ifndef CPROVER_FUNCTION_H
#define CPROVER_FUNCTION_H

#include <util/type.h>

class function_typet:public typet
{
public:
  function_typet():typet(ID_function)
  {
    subtypes().resize(2);
  }

  class variablet:public irept
  {
  public:
    irep_idt get_identifier() const
    {
      return get(ID_identifier);
    }

    void set_identifier(const irep_idt &identifier)
    {
      return set(ID_identifier, identifier);
    }
    
    typet &type()
    {
      return (typet &)add(ID_type);
    }

    const typet &type() const
    {
      return (const typet &)find(ID_type);
    }
  };

  using variablest=std::vector<variablet>;

  variablest &variables()
  {
    return (variablest &)subtypes()[0].subtypes();
  }

  const variablest &variables() const
  {
    return (const variablest &)subtypes()[0].subtypes();
  }

  variablet &add_variable()
  {
    auto &v=variables();
    v.push_back(variablet());
    return v.back();
  }

  typet &range()
  {
    return subtypes()[1];
  }

  const typet &range() const
  {
    return subtypes()[1];
  }
};

#endif
