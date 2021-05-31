using System;
using System.Collections.Generic;
using System.Linq;

namespace NineDigitProblem
{
    class Program
    {
        static void Main()
        {
            Console.WriteLine(x(new [] {1, 2, 3, 4, 5, 6, 7, 8, 9}, 0, 0));
        }

        static int x(IEnumerable<int> r, int v, int l)
        {
            return (l == 9 ? v : 0) + (from i in r
                                       where ((v*10 + i)%(l + 1)) == 0
                                       select x(r.Where(j => j != i), v*10 + i, l + 1)).Sum();
        }
    }
}
