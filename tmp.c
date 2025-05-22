#include <limits.h>

/*@
    // Prevent signed integer overflow: the sum fits in the C int range
    requires a <= INT_MAX - b && a >= INT_MIN - b;
    assigns \nothing;
    ensures \result == a + b;
*/
int add(int a, int b)
{
    return a + b;
}