/*@
  // Pre-condition: The function requires two integer inputs 'a' and 'b'.
  // No specific constraints on 'a' and 'b', can be any integers.
  requires \true;

  // Post-condition: The function ensures that the result returned is equal 
  // to the sum of 'a' and 'b'.
  ensures \result == a + b;

  // Assigns clause: The function does not modify any global or static variables.
  assigns \nothing;
*/
int add(int a, int b) {
  /*@
    // Inside the function, we can assert that the result of the addition
    // is indeed equal to the sum of 'a' and 'b'. This helps verify 
    // correctness of the addition performed.
    assert \result == a + b;

    // Result variable is implicitly defined by the return statement.
  */
  return a + b;
}