#include <iostream>

#include <torch/torch.h>

class synth_net : public torch::nn::Module
{
public:
  torch::nn::Linear fc1 = nullptr, fc2 = nullptr;

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

void train(
  const std::size_t epoch,
  synth_net &net,
  torch::optim::SGD &optimizer)
{
  size_t batch_index = 0;

  {
    // reset gradients
    optimizer.zero_grad();

    // Execute the model on the input data
    torch::Tensor data;
    auto prediction = net.forward(data);

    // Compute loss value
    torch::Tensor label;
    auto loss = torch::binary_cross_entropy(prediction, label);

    // Compute gradients of the loss w.r.t. the parameters of our model
    loss.backward();

    // Update the parameters based on the calculated gradients
    optimizer.step();

    if(batch_index++ % 10 == 0)
    {
      std::cout << "Epoch: " << epoch << " | Batch: " << batch_index
                << " | Loss: " << loss << std::endl;
    }
  }
}

int main()
{
  synth_net net;

  torch::optim::SGD optimizer(net.parameters(), /*lr=*/0.1);

  for(size_t epoch = 1; epoch <= 10; ++epoch)
  {
    train(epoch, net, optimizer);
  }

  // Serialize the net
  //torch::save(net, "synth_net.pt");
}
