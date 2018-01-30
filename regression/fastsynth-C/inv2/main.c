__CPROVER_bool EXPRESSION_inv(int x);

void main (void)
{
// base case
  int x=0;
  __CPROVER_assert(EXPRESSION_inv(x),"");

 // step case
 __CPROVER_havoc_object(&x);

 //assume invariant holds
 if(EXPRESSION_inv(x))
 {
   __CPROVER_assert(x<100005,"");

   // transition
   if(x <= 100000)
   {
     x++;

     // re-establish invariant
     __CPROVER_assert(EXPRESSION_inv(x),"");
   }
 }
}
