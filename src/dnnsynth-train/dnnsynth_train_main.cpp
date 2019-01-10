#include <iostream>

#include <torch/torch.h>

class synth_net : public torch::nn::Module
{
public:
  torch::nn::Linear fc1 = nullptr;
  torch::nn::Linear fc2 = nullptr;

  synth_net()
  {
    fc1 = register_module("fc1", torch::nn::Linear(8, 64));
    fc2 = register_module("fc2", torch::nn::Linear(64, 1));
  }

  torch::Tensor forward(torch::Tensor x)
  {
    x = torch::relu(fc1->forward(x));
    x = torch::dropout(x, /*p=*/0.5, /*train=*/true);
    x = torch::sigmoid(fc2->forward(x));
    return x;
  }
};

struct datat
{
  torch::Tensor data, labal;
};

std::vector<datat> produce_training_data()
{
  std::vector<datat> result;

  return result;
}

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

int main()
{
  synth_net net;

  torch::optim::SGD optimizer(net.parameters(), /*lr=*/0.1);

  std::vector<datat> training_data =
    produce_training_data();

  for(size_t epoch = 1; epoch <= 3; ++epoch)
  {
    train(epoch, net, training_data optimizer);
  }

  // Serialize the net
  torch::serialize::OutputArchive o;
  net.save(o);
  o.save_to("synthnet.pt");
}
