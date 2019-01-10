#include <torch/torch.h>

#include "produce_training_data.h"

class synth_net;

void train(
  const std::size_t epoch,
  synth_net &net,
  const std::vector<datat> &training_data,
  torch::optim::SGD &optimizer);
