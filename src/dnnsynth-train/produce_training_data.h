#ifndef FASTSYNTH_PRODUCE_TRAINING_DATA_H
#define FASTSYNTH_PRODUCE_TRAINING_DATA_H

#include <torch/torch.h>

struct datat
{
  torch::Tensor input, label;
};

std::vector<datat> produce_training_data();

#endif
