/*@
    // Ensures the result is the sum of two integers a and b.
    // Both a and b are within the range of int to avoid overflow.
    requires 0 <= a + b <= 214748364 ;
    ensures  \result == a + b;
    assigns  \nothing;
*/
int add(int a, int b)
{
    return a + b;
}