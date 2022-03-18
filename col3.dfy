/*
   Dafny implementation of backtracking for the 3-COL problem.
   Author: Stefan Ciobaca (stefan.ciobaca@gmail.com)

   3-COL
   Input: a graph G
   Output: is G 3-colorable? (plus witness if colorable)
 */

/*
   Checks whether the tuple n, s, f represents a valid graph.
   - n represents the number of nodes;
   - the array s, f represent the edges (there is an edge between s[i] and f[i] for each i).
*/
function isGraph(n : int, s : array<int>, f : array<int>) : bool
	reads *;
{
	s.Length == f.Length &&
		(forall i :: 0 <= i < s.Length ==> s[i] != f[i]) &&
		(forall i :: 0 <= i < s.Length ==> 0 <= s[i] < n) &&
		(forall i :: 0 <= i < s.Length ==> 0 <= f[i] < n)
}

/*
   Checks whether "coloring" represents a valid coloring of the graph.
   - the three colors are 0, 1, and 2;
*/
function isSolution(coloring : seq<int>, n : int, s : array<int>, f : array<int>) : bool
	reads *;
	requires isGraph(n, s, f);
{
	|coloring| == n &&
		forall i :: 0 <= i < n ==> 0 <= coloring[i] <= 2 &&
		forall j :: 0 <= j < s.Length ==> coloring[s[j]] != coloring[f[j]]
}

/*
   Checks whether "coloring" represents a valid partial coloring of the graph.
   - the three colors are 0, 1, and 2;
   - it is allowed to have nodes not yet colored.
*/
function method isPartialSolution(coloring : seq<int>, n : int, s : array<int>, f : array<int>) : bool
	reads *;
	requires isGraph(n, s, f);
{
	|coloring| <= n &&
		forall i :: 0 <= i < |coloring| ==> 0 <= coloring[i] <= 2 &&
		forall j :: 0 <= j < s.Length && s[j] < |coloring| && f[j] < |coloring| ==> coloring[s[j]] != coloring[f[j]]
}

/*
  The core of the backtracking algorithm.
  Checks whether the partial coloring "sol" can be extended to a full coloring.

  The result is a sequence of length 0 if no extension of sol is a full coloring.
  The result is a valid coloring if some extension of sol is a full coloring.
*/
method back(sol : seq<int>, n : int, s : array<int>, f : array<int>) returns (r : seq<int>)
	requires isGraph(n, s, f);
	requires n >= 1;
	requires 0 <= |sol| <= n;
	requires isPartialSolution(sol, n, s, f);
	ensures |r| == 0 ==> forall coloring : seq<int> :: sol <= coloring ==> !isSolution(coloring, n, s, f);
	ensures |r| > 0 ==> sol <= r && isSolution(r, n, s, f);
	decreases n - |sol|;
{
	if (|sol| == n) {
    // The partial solution "sol" already has colors for all nodes,
    // hence it is a (full) solution.
		r := sol; 
	} else {
		var i := 0;
    // Try to extend the partial solution by the colors 0, 1, and 2 for the next node.
		while (i <= 2)
			invariant forall j :: 0 <= j < i ==>
			  forall coloring : seq<int> :: sol + [j] <= coloring ==> !isSolution(coloring, n, s, f);
		{
			if (isPartialSolution(sol + [i], n, s, f)) {
				var r1 : seq<int> := back(sol + [i], n, s, f);
				if (|r1| != 0) {
          // If the partial solution "sol + [i]" can be extended to a (full) solution "r1",
          // then "r1" is also an extension of "sol" and we return it.
					r := r1;
					return;
				}
			}
			i := i + 1;
		}
    // At this point "sol + [0]", "sol + [1]", and "sol + [2]" cannot be extended to a
    // (full) solution. Therefore "sol" cannot be extended either.
		assert forall coloring : seq<int> :: isSolution(coloring, n, s, f) && sol <= coloring ==>
			(sol + [0] <= coloring || sol + [1] <= coloring || sol + [2] <= coloring);
		r := [];
	}
}

/*
  The entry point.
*/
method color(n : int, s : array<int>, f : array<int>) returns (r : seq<int>)
	requires isGraph(n, s, f);
	requires n >= 1;
	ensures |r| == 0 ==> forall coloring : seq<int> :: !isSolution(coloring, n, s, f);
	ensures |r| > 0 ==> isSolution(r, n, s, f);
{
	r := back([], n, s, f);
}
