#include <iostream>

#include "synth_net.h"
#include "train.h"
#include "produce_training_data.h"

int main()
{
  synth_net net;

  torch::optim::SGD optimizer(net.parameters(), /*lr=*/0.1);

  std::vector<datat> training_data =
    produce_training_data();

  for(size_t epoch = 1; epoch <= 3; ++epoch)
  {
    train(epoch, net, training_data, optimizer);
  }

  // Serialize the net
  torch::serialize::OutputArchive o;
  net.save(o);
  o.save_to("synthnet.pt");
}
