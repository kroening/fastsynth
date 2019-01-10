#include "train.h"
#include "synth_net.h"

void train(
  const std::size_t epoch,
  synth_net &net,
  const std::vector<datat> &training_data,
  torch::optim::SGD &optimizer)
{
  size_t batch_index = 0;

  for(unsigned i=0; i<training_data.size(); i++, batch_index++)
  {
    // reset gradients
    optimizer.zero_grad();

    // get the data
    const auto &data = training_data[batch_index];

    // Execute the model on the input data
    auto prediction = net.forward(data.input);

    // Compute loss value
    auto loss = torch::binary_cross_entropy(prediction, data.label);

    // Compute gradients of the loss
    loss.backward();

    // Update the parameters based on the calculated gradients
    optimizer.step();

    if(batch_index % 10 == 0)
    {
      std::cout << "Epoch: " << std::setw(2) << epoch
                << " | Batch: " << std::setw(3) << batch_index
                << " | Loss: "
                << std::fixed << std::setw(5) << std::setprecision(5)
                << loss.data<float>()[0] << '\n';
    }
  }
}
