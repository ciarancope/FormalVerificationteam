/*** Even ***/

 ghost predicate isEven(n: int) {
  exists m: int :: n == 2 * m
}
lemma EvenModulo(n: int)
  ensures isEven(n) ==> n % 2 == 0
{}
lemma ModuloEven(n: int)
  ensures n % 2 == 0 ==> isEven(n)
{
	if n % 2 == 0 {
	  var m := n / 2;
	  assert n == 2 * m;
	}
}
function checkEven(n: int) : (b: bool) {
	n % 2 == 0
}
lemma checkEvenCorrect(n: int)
  ensures checkEven(n) <==> isEven(n)
{
	EvenModulo(n);
	ModuloEven(n);
}
lemma EvenTimes(n1: int, n2: int)
  ensures isEven(n1) || isEven(n2) ==> isEven(n1 * n2)
{
  if isEven(n1) {
	var m1 := n1 / 2;
	assert n1 * n2 == 2 * (m1 * n2);
  } else if isEven(n2) {
	var m2 := n2 / 2;
	assert n1 * n2 == 2 * (n1 * m2);
  }
}

/*** Odd ***/

ghost predicate isOdd(n: int) {
  exists m: int :: n == 2 * m + 1
}
lemma OddModulo(n: int)
  ensures isOdd(n) ==> n % 2 != 0
{}
lemma ModuloOdd(n: int)
  ensures n % 2 != 0 ==> isOdd(n)
{ // TODO
	if n % 2 != 0 {
	  var m := n / 2;
	  assert n == 2 * m + 1;
	}
}
function checkOdd(n: int): (b: bool) {
	n % 2 != 0
}
lemma checkOddCorrect(n: int)
  ensures checkOdd(n) <==> isOdd(n)
{ // TODO
	OddModulo(n);
	ModuloOdd(n);
}
lemma OddTimesOdd(n1: int, n2: int)
  ensures isOdd(n1) && isOdd(n2) ==> isOdd(n1 * n2)
{ // TODO
  if isOdd(n1) && isOdd(n2) {
    var m1 := n1 / 2;
    var m2 := n2 / 2;
    assert n1 * n2 == 2 * (2 * m1 * m2 + m1 + m2) + 1;
  }
}

/*** Even & Odd ***/

lemma NotEvenANDOdd(n: int)
  ensures !(isEven(n) && isOdd(n))
{ 
}

lemma EvenOrOdd(n: int)
  ensures isEven(n) || isOdd(n)
{ // TODO
  if n % 2 == 0 {
	ModuloEven(n);
  } else {
	ModuloOdd(n);
  }
}

lemma EvenTimesOdd(n1: int, n2: int)
  ensures isEven(n1) && isOdd(n2) ==> isEven(n1 * n2)
{ // TODO
  if isEven(n1) && isOdd(n2) {
    var m1 := n1 / 2;
    var m2 := n2 / 2;
    assert n1 * n2 == 2 * (2 * m1 * m2 + m1);
  }
}

function invertParity(n: int): (m: int) {
	n + 1
}

lemma InvertParityCorrect(n: int)
  ensures isEven(n) ==> isOdd(invertParity(n))
  ensures isOdd(n) ==> isEven(invertParity(n))
{ // TODO
	if isEven(n) {
		var m := invertParity(n);
		ModuloOdd(m);
	} else {
		var m := invertParity(n);
		ModuloEven(m);
	}
}


/*** Even and Odd Sets ***/

/* A set is represented as a sequence with no duplicates */
predicate isSet(s: seq<int>) {
  forall i, j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == s[j] ==> i == j // TODO
}

// // hint don't use return statements. Set b instead.
// method checkSet(s: seq<int>) returns (b: bool)
//   // requires isSet(s)  // We had this too
//   ensures b <==> isSet(s) //TODO
// { // TODO: fill in your code here and prove method correct
// b := true;                    // Assume to be true at the beginning 
// var i := 0;                   // Outer while loop 
// var j := 0;                   // Inner while loop
// while i < |s| && b                // While loop to sort through set, stop if i reaches the end or duplicate found
//     {
//     j := i + 1;
//     while j < |s| && b       // Stop if j reaches the end or duplicate found
//       {
//        if s[i] == s[j] {
//           b := false; // Duplicate found, set b to false 
//         }
//         j := j + 1;
//       }
//     i := i + 1;
//     }
// }

// hint don't use return statements. Set b instead.
method checkSet(s: seq<int>) returns (b: bool)
  ensures b <==> isSet(s)
{
  b := true;
  var i := 0;

  // If we ever discover a duplicate, we store the witnessing indices here
  ghost var wi: int := 0;
  ghost var wj: int := 0;

  while i < |s| && b
    invariant 0 <= i <= |s|
    // If b is still true, then every earlier index p < i has been proven distinct
    // from every later index q > p (i.e., all duplicates with first index < i are ruled out).
    invariant b ==> (forall p, q :: 0 <= p < i && p < q < |s| ==> s[p] != s[q])
    // If b is false, we have a concrete duplicate witness.
    invariant !b ==> (0 <= wi < wj < |s| && s[wi] == s[wj])
  {
    var j := i + 1;
    while j < |s| && b
      invariant 0 <= i < |s|
      invariant i + 1 <= j <= |s|
      // If b is still true, then s[i] is distinct from all elements we have checked so far in this inner loop.
      invariant b ==> (forall k :: i < k < j ==> s[i] != s[k])
      // Carry the outer progress fact into the inner loop.
      invariant b ==> (forall p, q :: 0 <= p < i && p < q < |s| ==> s[p] != s[q])
      // If b is false, we have a concrete duplicate witness.
      invariant !b ==> (0 <= wi < wj < |s| && s[wi] == s[wj])
    {
      if s[i] == s[j] {
        b := false;
        wi := i;
        wj := j;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}


/* An even set is a set where all elements are even */
ghost predicate isEvenSet(s: seq<int>) {
 isSet(s) && forall x :: x in s ==> isEven(x) // TODO
}

method checkEvenSet(s: seq<int>) returns (b: bool)
  //  requires isSet(s) 

  ensures b <==> isEvenSet(s)
{ // TODO: fill in your code here and prove method correct 
  b := true; // Initialise at the start
  var i := 0;
  while i < |s| 
    {
      if s[i] % 2 != 0 {
        b := false; 
      } 
      i := i + 1;
    }
}


/* An odd set is a set where all elements are odd */
ghost predicate isOddSet(s: seq<int>) {
  isSet(s) && forall x :: x in s ==> isOdd(x) // TODO
}

method checkOddSet(s: seq<int>) returns (b: bool)
  ensures b <==> isOddSet(s)
{ // TODO: fill in your code here and prove method correct

  b := true; // Initialise at the start
  var i := 0;
  while i < |s| 
      invariant 0 <= i <= |s|
      decreases |s| - i
      invariant b ==> (forall v :: 0 <= v < i ==> (s[v] % 2 != 0))
    {
      if s[i] % 2 == 0 {
        b := false; 
      } 
      i := i + 1;
    }
    assert i == |s|;
}

/*** Set Operations ***/

/* Adds n to a set s, making sure it remains a set */
// Hint: use recursion
method addToSet(s: seq<int>, n: int) returns (b: seq<int>)
  requires isSet(s)
  ensures isSet(b)
  ensures forall x :: (0 <= x < |b|) ==> (b[x] in s || b[x] == n)
  ensures forall x :: (0 <= x < |s|) ==>  s[x] in b
  ensures n in s ==> b == s
  ensures !(n in s) ==> b == s + [n]
  ensures isEvenSet(s) && isEven(n) ==> isEvenSet(b)
  ensures isOddSet(s) && isOdd(n) ==> isOddSet(b)
{ // TODO: fill in your code here and prove method correct
  if n !in s {
    b := s + [n];
    assert n == b[|b| - 1];
  } else {
    b := s;
  }
}

/* unions two sets s1 and s2, returning a new set t */
method union(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 || t[x] in s2)
  ensures forall x :: (0 <= x < |s1| ==> s1[x] in t)
  ensures forall x :: (0 <= x < |s2| ==> s2[x] in t)
  ensures isEvenSet(s1) && isEvenSet(s2) ==> isEvenSet(t)
  ensures isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
{
  var i := 0;
  t := s1;

  while i < |s2|
    invariant 0 <= i <= |s2|
    invariant isSet(t)
    // keep all of s1
    invariant forall x :: 0 <= x < |s1| ==> s1[x] in t
    // all processed elements of s2 are in t
    invariant forall k :: 0 <= k < i ==> s2[k] in t
    // t contains nothing except elements from s1 or s2
    invariant forall x :: x in t ==> x in s1 || x in s2
  {
    if s2[i] !in t {
      t := addToSet(t, s2[i]);
    }
    i := i + 1;
  }
}

/* intersects two sets s1 and s2, returning a new set t */
// method intersection(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
//   requires isSet(s1) && isSet(s2)
//   ensures isSet(t)
//   ensures forall x :: (0 <= x < |t| ==> t[x] in s1 && t[x] in s2)
//   ensures forall x, y :: (0 <= x < |s1| && 0 <= y < |s2| && s1[x] == s2[y]) ==> s1[x] in t
//   ensures isEvenSet(s1) ==> isEvenSet(t)
//   ensures isOddSet(s1) ==> isOddSet(t)
//   ensures isEvenSet(s1) && isOddSet(s2) ==> |t| == 0
// { // TODO: fill in your code here and prove method correct
//   // hint: you may need to call:
//   //  NotEvenANDOdd(s1[i]);
//   // at the appropriate place in your code to help Dafny prove correctness
//   var i := 0;
//   t := []; // Empty set if no overlap
//   while i < |s1| 
//     invariant 0 <= i <= |s1|
//     invariant isSet(t)
//   {
//     var j := 0; 
//     while j < |s2| 
//       invariant isSet(t)
//       invariant 0 <= j <= |s2|
//       {
//         if s1[i] == s2[j] {
//           t := addToSet(t, s1[i]);
//        }
//        j := j + 1;
//       }
//     i := i + 1; 
//   }
// }


method intersection(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 && t[x] in s2)
  ensures forall x, y :: (0 <= x < |s1| && 0 <= y < |s2| && s1[x] == s2[y]) ==> s1[x] in t
  ensures isEvenSet(s1) ==> isEvenSet(t)
  ensures isOddSet(s1) ==> isOddSet(t)
  ensures isEvenSet(s1) && isOddSet(s2) ==> |t| == 0
{
  var i := 0;
  t := [];
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(t)
    // Soundness in the *index form* that matches the postcondition:
    // everything currently stored in t is in (processed prefix of s1) and in s2.
    invariant forall p :: 0 <= p < |t| ==> t[p] in s1[..i] && t[p] in s2
    // Completeness for processed prefix: any s1[k] (k<i) that occurs in s2 is in t
    invariant forall k, l :: 0 <= k < i && 0 <= l < |s2| && s1[k] == s2[l] ==> s1[k] in t
    // Parity preservation
    // invariant isEvenSet(s1) ==> (forall p :: 0 <= p < |t| ==> isEven(t[p]))
    // invariant isOddSet(s1)  ==> (forall p :: 0 <= p < |t| ==> isOdd(t[p]))
    // Even-set ∩ odd-set is empty
    invariant isEvenSet(s1) && isOddSet(s2) ==> |t| == 0
    decreases |s1| - i
  {
    var j := 0;
    while j < |s2|
      invariant 0 <= j <= |s2|
      invariant isSet(t)
      // During inner loop we may add s1[i], so use prefix s1[..i+1]
      invariant forall p :: 0 <= p < |t| ==> t[p] in s1[..i+1] && t[p] in s2
      // Keep outer completeness for k<i
      invariant forall k, l :: 0 <= k < i && 0 <= l < |s2| && s1[k] == s2[l] ==> s1[k] in t
      // Inner progress: if s1[i] has matched among s2[0..j), then s1[i] is in t
      invariant (exists k :: 0 <= k < j && s2[k] == s1[i]) ==> s1[i] in t
      // Preserve disjointness claim inside inner loop too
      invariant isEvenSet(s1) && isOddSet(s2) ==> |t| == 0
      decreases |s2| - j
    {
      if s1[i] == s2[j] {
        t := addToSet(t, s1[i]);
      }
      j := j + 1;
    }
    i := i + 1;
  }

  // DELETE the incorrect "product" bridge assertion (it doesn't belong in intersection)
  // assert forall v1, v2 :: v1 in s1 && v2 in s2 ==> v1 * v2 in t by { }
}

/* difference of two sets s1 and s2, returning a new set t = s1 - s2 */
// method difference(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
//   requires isSet(s1) && isSet(s2)
//   ensures isSet(t)
//   ensures forall x :: (0 <= x < |t| ==> t[x] in s1 && !(t[x] in s2))
//   ensures forall x :: (0 <= x < |s1| && !(s1[x] in s2)) ==> s1[x] in t
//   ensures isEvenSet(s1) ==> isEvenSet(t)
//   ensures isOddSet(s1) ==> isOddSet(t)
//   ensures isEvenSet(s1) && isOddSet(s2) ==> t == s1 // hint: don't use addToSet in your code -- use t + [s1[i]] instead
// { // TODO: fill in your code here and prove method correct
//   // hint: you may need to call:
//   //  NotEvenANDOdd(s1[i]);
//   // at the appropriate place in your code to help Dafny prove correctness
//   var i := 0;
//   t := []; // Empty set if no different elements
//   while i < |s1| 
//     invariant 0 <= i <= |s1|
//     { 
//       if s1[i] !in s2 {  // Don't include anything from s1 that is also in s2.
//         t := addToSet(t, s1[i]);
//         assert isSet(t);
//       }
//       i := i + 1;
//     }
// }

method difference(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 && !(t[x] in s2))
  ensures forall x :: (0 <= x < |s1| && !(s1[x] in s2)) ==> s1[x] in t
  ensures isEvenSet(s1) ==> isEvenSet(t)
  ensures isOddSet(s1) ==> isOddSet(t)
  ensures isEvenSet(s1) && isOddSet(s2) ==> t == s1
{
  var i := 0;
  t := [];

  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(t)

    // Soundness: everything in t came from the processed prefix of s1 and is not in s2
    invariant forall p :: 0 <= p < |t| ==> t[p] in s1[..i] && !(t[p] in s2)

    // Completeness: every processed element of s1 that is not in s2 is in t
    invariant forall k :: 0 <= k < i && !(s1[k] in s2) ==> s1[k] in t

    // Parity preservation (enough to imply isEvenSet(t)/isOddSet(t) at the end)
    invariant isEvenSet(s1) ==> (forall p :: 0 <= p < |t| ==> isEven(t[p]))
    invariant isOddSet(s1)  ==> (forall p :: 0 <= p < |t| ==> isOdd(t[p]))

    // Special case: even-set minus odd-set keeps all elements, in order
    invariant isEvenSet(s1) && isOddSet(s2) ==> t == s1[..i]

    decreases |s1| - i
  {
    // If s1 is all-even and s2 is all-odd, then s1[i] cannot be in s2
    if isEvenSet(s1) && isOddSet(s2) && s1[i] in s2 {
      assert isEven(s1[i]); // since s1[i] in s1 and isEvenSet(s1)
      // assert isOdd(s1[i]);  // since s1[i] in s2 and isOddSet(s2)
      // NotEvenANDOdd(s1[i]);
    }
    if s1[i] !in s2 {
      // Help Dafny use addToSet's "append" postcondition in the special case:
      // if isEvenSet(s1) && isOddSet(s2) {
        // from invariant t == s1[..i] and isSet(s1), s1[i] is not in the prefix
        // assert s1[i] !in s1[..i];
        // assert s1[i] !in t;
      // }
      t := addToSet(t, s1[i]);
      // // Re-establish the special-case shape invariant after the append
      // if isEvenSet(s1) && isOddSet(s2) {
      //   assert t == s1[..i] + [s1[i]];
      //   assert t == s1[..i+1];
      // }
    }
    i := i + 1;
  }
  // // Finish the special-case postcondition using i == |s1|
  // if isEvenSet(s1) && isOddSet(s2) {
  //   assert i == |s1|;
  //   assert t == s1[..i];
  //   assert t == s1;
  // }
}

/* multiplies each element of a set s by n, returning a new set t */
// method setScale(s: seq<int>, n: int) returns (t: seq<int>)
//   requires isSet(s)
//   ensures isSet(t)
//   ensures forall x :: (0 <= x < |t| ==> exists i :: 0<= i < |s| && t[x] == s[i] * n)
//   ensures forall x :: (0 <= x < |s| ==> s[x] * n in t)
//   ensures isEvenSet(s) || isEven(n) ==> isEvenSet(t)
//   ensures isOddSet(s) && isOdd(n) ==> isOddSet(t)
// { // TODO: fill in your code here and prove method correct
//   // hint: you may need to call:
//   //  EvenTimes(s[i], n);
//   //  OddTimesOdd(s[i], n);
//   // at the appropriate place in your code to help Dafny prove correctness
//   var i := 0; 
//   t := [];
//   var placeholder := 0;
//   while i < |s| 
//     invariant 0 <= i <= |s|
//     invariant isSet(s)
//     decreases |s| - i
//     {
//       placeholder := s[i] * n;
//       t := addToSet(t, placeholder);
//       i := i + 1;
//     }
// }

/* multiplies each element of a set s by n, returning a new set t */
method setScale(s: seq<int>, n: int) returns (t: seq<int>)
  requires isSet(s)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> exists i :: 0<= i < |s| && t[x] == s[i] * n)
  ensures forall x :: (0 <= x < |s| ==> s[x] * n in t)
  ensures isEvenSet(s) || isEven(n) ==> isEvenSet(t)
  ensures isOddSet(s) && isOdd(n) ==> isOddSet(t)
{
  var i := 0;
  t := [];
  var placeholder := 0;

  while i < |s|
    invariant 0 <= i <= |s|
    invariant isSet(t)

    // Soundness: every element in t is some scaled element from the processed prefix s[..i]
    invariant forall p :: 0 <= p < |t| ==> exists k :: 0 <= k < i && t[p] == s[k] * n

    // Completeness: every processed element's scale is in t
    invariant forall k :: 0 <= k < i ==> s[k] * n in t

    // Parity preservation
    invariant (isEvenSet(s) || isEven(n)) ==> isEvenSet(t)
    invariant (isOddSet(s) && isOdd(n)) ==> isOddSet(t)

    decreases |s| - i
  {
    ghost var t0 := t;
    ghost var i0 := i;

    placeholder := s[i] * n;

    // Prove parity of the element we are about to add (needed to reuse addToSet's parity ensures)
    if isEvenSet(s) || isEven(n) {
      if isEven(n) {
        EvenTimes(s[i], n);
      } else {
        // then isEvenSet(s)
        assert isEvenSet(s);
        assert s[i] in s;
        assert isEven(s[i]);
        EvenTimes(s[i], n);
      }
      assert isEven(placeholder);
    }

    if isOddSet(s) && isOdd(n) {
      assert s[i] in s;
      assert isOdd(s[i]);
      OddTimesOdd(s[i], n);
      assert isOdd(placeholder);
    }

    // Add scaled element (deduplicated)
    t := addToSet(t, placeholder);

    // // Useful normalization: either unchanged or appended
    // if placeholder in t0 {
    //   assert t == t0;
    // } else {
    //   assert t == t0 + [placeholder];
    // }

    i := i + 1;

    // // Re-establish "completeness" for the newly processed index (k == i0)
    // assert s[i0] * n == placeholder;
    // assert placeholder in t; // holds in both branches above
    // assert s[i0] * n in t;
  }
}

/* multiplies each element of a set s by n, returning a new set t */
method setProduct(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: x in t ==> exists i1, j1 :: 0<= i1 < |s1| && 0<= j1 < |s2| && x == s1[i1] * s2[j1]
  ensures forall i1, j1 :: i1 in s1 && j1 in s2 ==> i1 * j1 in t
  ensures isEvenSet(s1) || isEvenSet(s2) ==> isEvenSet(t)
  ensures isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
{ // TODO: fill in your code here and prove method correct
var i := 0; 
  var j := 0;
  t := []; 
  while i < |s1| 
    invariant 0 <= i <= |s1|
    decreases |s1| - i 
    decreases |s2| - i 
    {
      while j < |s2| {
        var placeholder := s1[i] * s2[j];
        t := addToSet(t, placeholder);
        j := j + 1;
      }
      i := i + 1;
    }
}



// /* converts an even set to an odd set by inverting the parity of each element  */
// method invertParitySet(s: seq<int>) returns (t:seq<int>)
//   requires isEvenSet(s) || isOddSet(s)
//   ensures isEvenSet(s) ==> isOddSet(t)
//   ensures isOddSet(s) ==> isEvenSet(t)
//   ensures |t| == |s|
//   ensures forall i :: 0 <= i < |s| ==> t[i] == invertParity(s[i])
// { // TODO: fill in your code here and prove method correct
//   // hint: you may need to call:
//   //  InvertParityCorrect(s[i]);
//   // at the appropriate place in your code to help Dafny prove correctness
//   t := [];
//   var i := 0;
//   while i < |s| 
//     invariant 0 <= i <= |s|
//     decreases |s| - i
//     {
//       t := addToSet(t, invertParity(s[i]));
//       i := i + 1; 
//     }
// }

method invertParitySet(s: seq<int>) returns (t:seq<int>)
  requires isEvenSet(s) || isOddSet(s)
  ensures isEvenSet(s) ==> isOddSet(t)
  ensures isOddSet(s) ==> isEvenSet(t)
  ensures |t| == |s|
  ensures forall i :: 0 <= i < |s| ==> t[i] == invertParity(s[i])
{
  // Pull out isSet(s) from the disjunction
  if isEvenSet(s) {
    assert isSet(s);
  } else {
    assert isOddSet(s);
    assert isSet(s);
  }
  assert isSet(s);

  t := [];
  var i := 0;

  while i < |s|
    invariant 0 <= i <= |s|
    invariant isSet(t)
    invariant |t| == i
    invariant forall k :: 0 <= k < i ==> t[k] == invertParity(s[k])
    decreases |s| - i
  {
    var t0 := t;
    var i0 := i;

    var v := invertParity(s[i0]);

    // Show v is NOT already in t0, so addToSet will append and length increases
    if v in t0 {
      ghost var p: int :| 0 <= p < |t0| && t0[p] == v;

      // bounds rewrite using |t0| == i0
      assert |t0| == i0;
      assert 0 <= p < i0;

      // use mapping invariant on the old prefix
      assert t0[p] == invertParity(s[p]);
      assert v == invertParity(s[i0]);
      assert invertParity(s[p]) == invertParity(s[i0]);

      // injective: (a+1 == b+1) ==> a == b
      assert s[p] + 1 == s[i0] + 1;
      assert s[p] == s[i0];

      // contradict isSet(s): equal values imply equal indices
      assert isSet(s);
      assert 0 <= p < |s| && 0 <= i0 < |s|;
      assert p == i0;
      assert false; // but we also have p < i0
    }
    assert !(v in t0);

    t := addToSet(t0, v);

    // Since v ∉ t0, addToSet must append
    assert t == t0 + [v];

    i := i0 + 1;

    // Re-establish |t| == i
    assert |t| == |t0| + 1;
    assert |t0| == i0;
    assert |t| == i;

    // Re-establish mapping on the extended prefix
    assert forall k :: 0 <= k < i ==> t[k] == invertParity(s[k]) by {
      forall k | 0 <= k < i
        ensures t[k] == invertParity(s[k])
      {
        if k < i0 {
          assert t[k] == t0[k];                 // because t == t0 + [v]
          assert t0[k] == invertParity(s[k]);    // old invariant
        } else {
          assert k == i0;
          assert t[k] == v;                      // last element of append
          assert v == invertParity(s[i0]);
        }
      }
    }
  }

  // Finish index/length postconditions from invariants with i == |s|
  assert i == |s|;
  assert |t| == |s|;
  assert forall k :: 0 <= k < |s| ==> t[k] == invertParity(s[k]);

  // Parity postconditions (proved from definitions; no reliance on InvertParityCorrect)
  if isEvenSet(s) {
    assert forall x :: x in t ==> isOdd(x) by {
      forall x | x in t
        ensures isOdd(x)
      {
        ghost var p: int :| 0 <= p < |t| && t[p] == x;

        // use mapping and even-set property
        assert t[p] == invertParity(s[p]);
        assert s[p] in s;
        assert forall y :: y in s ==> isEven(y);
        assert isEven(s[p]);

        ghost var m: int :| s[p] == 2 * m;
        assert x == t[p];
        assert x == s[p] + 1;
        assert x == 2 * m + 1;
        assert isOdd(x);
      }
    }
    assert isOddSet(t);
  }

  if isOddSet(s) {
    assert forall x :: x in t ==> isEven(x) by {
      forall x | x in t
        ensures isEven(x)
      {
        ghost var p: int :| 0 <= p < |t| && t[p] == x;

        assert t[p] == invertParity(s[p]);
        assert s[p] in s;
        assert forall y :: y in s ==> isOdd(y);
        assert isOdd(s[p]);

        ghost var m: int :| s[p] == 2 * m + 1;
        assert x == t[p];
        assert x == s[p] + 1;
        assert x == 2 * (m + 1);
        assert isEven(x);
      }
    }
    assert isEvenSet(t);
  }
}

