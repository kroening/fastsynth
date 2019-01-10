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
