#include "produce_training_data.h"

#include <cstdlib>

std::vector<datat> produce_training_data()
{
  srandom(0);

  std::vector<datat> result;

  // relation p0 <= p1
  for(std::size_t i=0; i<1000; i++)
  {
    result.push_back(datat());
    auto &data = result.back();

    data.input = torch::zeros(8);
    data.input[0] = (int64_t)random();
    data.input[1] = (int64_t)random();

    data.label = torch::zeros(1);
    data.label[0] = (int64_t) (data.input.data<float>()[0]<=data.input.data<float>()[1]);
  }

  return result;
}
