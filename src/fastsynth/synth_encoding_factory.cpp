#include <fastsynth/synth_encoding_factory.h>
#include <fastsynth/synth_encoding.h>

synth_encoding_factoryt default_synth_encoding_factory()
{
  return
    []() { return std::unique_ptr<synth_encodingt>(new synth_encodingt()); };
}
