
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

// ...existing code...

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
      invariant 0 <= i <= |s|
      decreases |s| - i
      invariant b ==> (forall v :: 0 <= v < i ==> (s[v] % 2 == 0))
    {
      if s[i] % 2 != 0 {
        b := false; 
      } 
      i := i + 1;
    }
    assert i == |s|;
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
{ // TODO: fill in your code here and prove method correct
  var i := 0; 
  // var counter := 0; 
  t := s1;  // Initialise t to be equal the first set 
  while i < |s2| 
    {
      if s2[i] !in t {
        t := addToSet(t, s2[i]);
      }
      i := i + 1;
    }
}

/* intersects two sets s1 and s2, returning a new set t */
method intersection(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 && t[x] in s2)
  ensures forall x, y :: (0 <= x < |s1| && 0 <= y < |s2| && s1[x] == s2[y]) ==> s1[x] in t
  ensures isEvenSet(s1) ==> isEvenSet(t)
  ensures isOddSet(s1) ==> isOddSet(t)
  ensures isEvenSet(s1) && isOddSet(s2) ==> |t| == 0
{ // TODO: fill in your code here and prove method correct
  // hint: you may need to call:
  //  NotEvenANDOdd(s1[i]);
  // at the appropriate place in your code to help Dafny prove correctness
  var i := 0;
  t := []; // Empty set if no overlap
  while i < |s1| 
    invariant 0 <= i <= |s1|
    invariant isSet(t)
  {
    var j := 0; 
    while j < |s2| 
      invariant isSet(t)
      invariant 0 <= j <= |s2|
      {
        if s1[i] == s2[j] {
          t := addToSet(t, s1[i]);
       }
       j := j + 1;
      }
    i := i + 1; 
  }
}

/* difference of two sets s1 and s2, returning a new set t = s1 - s2 */
method difference(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 && !(t[x] in s2))
  ensures forall x :: (0 <= x < |s1| && !(s1[x] in s2)) ==> s1[x] in t
  ensures isEvenSet(s1) ==> isEvenSet(t)
  ensures isOddSet(s1) ==> isOddSet(t)
  ensures isEvenSet(s1) && isOddSet(s2) ==> t == s1 // hint: don't use addToSet in your code -- use t + [s1[i]] instead
{ // TODO: fill in your code here and prove method correct
  // hint: you may need to call:
  //  NotEvenANDOdd(s1[i]);
  // at the appropriate place in your code to help Dafny prove correctness
  var i := 0;
  t := []; // Empty set if no different elements
  while i < |s1| 
    invariant 0 <= i <= |s1|
    { 
      if s1[i] !in s2 {  // Don't include anything from s1 that is also in s2.
        t := addToSet(t, s1[i]);
        assert isSet(t);
      }
      i := i + 1;
    }
}

/* multiplies each element of a set s by n, returning a new set t */
method setScale(s: seq<int>, n: int) returns (t: seq<int>)
  requires isSet(s)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> exists i :: 0<= i < |s| && t[x] == s[i] * n)
  ensures forall x :: (0 <= x < |s| ==> s[x] * n in t)
  ensures isEvenSet(s) || isEven(n) ==> isEvenSet(t)
  ensures isOddSet(s) && isOdd(n) ==> isOddSet(t)
{ // TODO: fill in your code here and prove method correct
  // hint: you may need to call:
  //  EvenTimes(s[i], n);
  //  OddTimesOdd(s[i], n);
  // at the appropriate place in your code to help Dafny prove correctness
  var i := 0; 
  t := [];
  var placeholder := 0;
  while i < |s| 
    invariant 0 <= i <= |s|
    invariant isSet(s)
    decreases |s| - i
    {
      placeholder := s[i] * n;
      t := addToSet(t, placeholder);
      i := i + 1;
    }
}

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


/* converts an even set to an odd set by inverting the parity of each element  */
method invertParitySet(s: seq<int>) returns (t:seq<int>)
  requires isEvenSet(s) || isOddSet(s)
  ensures isEvenSet(s) ==> isOddSet(t)
  ensures isOddSet(s) ==> isEvenSet(t)
  ensures |t| == |s|
  ensures forall i :: 0 <= i < |s| ==> t[i] == invertParity(s[i])
{ // TODO: fill in your code here and prove method correct
  // hint: you may need to call:
  //  InvertParityCorrect(s[i]);
  // at the appropriate place in your code to help Dafny prove correctness
  t := [];
  var i := 0;
  while i < |s| 
    invariant 0 <= i <= |s|
    decreases |s| - i
    {
      t := addToSet(t, invertParity(s[i]));
      i := i + 1; 
    }
}
