#ifndef CPROVER_FASTSYNTH_SYNTH_ENCODING_FACTORY_H_
#define CPROVER_FASTSYNTH_SYNTH_ENCODING_FACTORY_H_

#include <memory>

/// Factory class used to instantiate configurable synth_encodingt instances.
typedef std::function<std::unique_ptr<class synth_encodingt>()>
  synth_encoding_factoryt;

/// Factory for the default synth_encodingt.
synth_encoding_factoryt default_synth_encoding_factory();

#endif /* SRC_FASTSYNTH_SYNTH_ENCODING_FACTORY_H_ */
