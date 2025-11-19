
/*** Even ***/

 ghost predicate isEven(n: int) {
  exists m: int :: n == 2 * m
}
function checkEven(n: int) : (b: bool) {
	n % 2 == 0
}
// The next three lemmas prove that modulo-based definition is equivalent to existential-based definition
lemma EvenModulo(n: int)
  ensures isEven(n) ==> n % 2 == 0
{}
lemma ModuloEven(n: int)
  ensures n % 2 == 0 ==> isEven(n)
{
	if n % 2 == 0 {
	  var m := n / 2;
	  assert n == 2 * m; // Hint for Dafny to choose n/2 as witness for the existential in the isEven predicate
	}
}
lemma checkEvenCorrect(n: int)
  ensures checkEven(n) <==> isEven(n)
{
	EvenModulo(n);
	ModuloEven(n);
}
// Useful lemma that may be used later
// It shows that the product of two integers is even if at least one of them is even
lemma EvenTimesAny(n1: int, n2: int)
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
function checkOdd(n: int): (b: bool) {
	n % 2 != 0
}
lemma OddModulo(n: int)
  ensures isOdd(n) ==> n % 2 != 0
{}
lemma ModuloOdd(n: int)
  ensures n % 2 != 0 ==> isOdd(n)
{ 
  if n % 2 != 0 {
    var m := n / 2;    // This should return the floor of the division, issues with pos & negs
    assert n == 2 * m + 1;
  }
}
lemma checkOddCorrect(n: int)
  ensures checkOdd(n) <==> isOdd(n)
{ // TODO: complete his proof
  OddModulo(n);
  ModuloOdd(n);
}

// The product of two odd numbers is always odd
lemma OddTimesOdd(n1: int, n2: int)
  ensures isOdd(n1) && isOdd(n2) ==> isOdd(n1 * n2)
{ 
  if isOdd(n1) && isOdd(n2) {
    var m1 := n1/2;
    var m2 := n2/2;
    assert n1 == 2 * m1 + 1; // n1 is odd
    assert n2 == 2 * m2 + 1; // n2 is odd
    // n1 * n2 = (2 * m1 + 1)(2 * m2 + 1) = 4*m1*m2 + 2*m1 +2*m2 + 1
    // n1 * n2 = 2(2*m1 + m1 + m2) + 1
    // n1 * n2 = m + 1
    var m := 2*(2*m1*m2+m1+m2); // 
    assert n1 * n2 == m + 1; // Product is odd
  }
}

/*** Even & Odd ***/

lemma NotEvenANDOdd(n: int)
  ensures !(isEven(n) && isOdd(n))
{ 
}

lemma EvenOrOdd(n: int)
  ensures isEven(n) || isOdd(n)
{ 
  if n % 2 == 0 { // If even 
    var m := n/2;
    assert n != 2 * m + 1; // Assert not odd
  } 
  if n % 2 != 0 { // If not even, check if odd 
    var m := n/2;
    assert n != 2 * m; // Assert not even
  }
}

function invertParity(n: int): (m: int) {
	n + 1
}

lemma InvertParityCorrect(n: int)
  ensures isEven(n) ==> isOdd(invertParity(n))
  ensures isOdd(n) ==> isEven(invertParity(n))
{ // TODO: complete this proof
  if isEven(n) {
    var m := n/2;
    assert invertParity(n) == 2 * m + 1;
    assert invertParity(n) == n + 1; 
    assert n + 1 == 2 * m + 1;
    assert invertParity(n) % 2 != 0;
    assert isOdd(invertParity(n));
    assert isOdd(2 * m + 1);
  }
  if isOdd(n){
    var m := n/2; 
    assert invertParity(n) == 2 * (m + 1);
    assert n + 1 == 2 * (m + 1);
    assert invertParity(n) == n + 1; 
    assert (n+1) % 2 == 0;
    assert (2 * (m + 1)) % 2 == 0; 
    assert invertParity(n) % 2 == 0;
    assert isEven(2 * m + 2);
    assert isEven(invertParity(n));
  }
}


/*** Even and Odd Sets ***/

/* A set is represented as a sequence with no duplicates */
predicate isSet(s: seq<int>) {
  forall i: int, j: int :: 0 <= i < |s| && 0 <= j < |s| && i != j ==> s[i] != s[j] 
}

// hint don't use return statements. Set b instead.
method checkSet(s: seq<int>) returns (b: bool)
  requires isSet(s)
  ensures b <==> isSet(s)
{ 
  b := true;                    // Assume to be true at the beginning 
  var i := 0;                   // Outer while loop 
  while i < |s| && b                // While loop to sort through set, stop if i reaches the end or duplicate found
    invariant 0 <= i <= |s|  // Invariant to confirm that i never exceeds the range
    decreases |s| - i
    invariant b ==> (forall u, v :: 0 <= u < i && 0 <= v < i && u != v ==> s[u] != s[v])
    invariant b ==> (forall u, v :: 0 <= u < i && i <= v < |s| ==> s[u] != s[v])
    {
    var j := i + 1;
    while j < |s| && b       // Stop if j reaches the end or duplicate found
      invariant 0 <= j <= |s|
      decreases |s| - j
      invariant b ==> (forall v :: i < v < j ==> s[i] != s[v])
      {
       if s[i] == s[j] {
          b := false; 
        }
        j := j + 1;
      }
    i := i + 1;
    }
}

/* An even set is a set where all elements are even */
ghost predicate isEvenSet(s: seq<int>) {
  forall i: int :: 0 <= i < |s| ==> isEven(s[i])
}

method checkEvenSet(s: seq<int>) returns (b: bool)
  requires isSet(s) 
  ensures b <==> isEvenSet(s)
{ 
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
  forall i: int :: 0 <= i < |s| ==> isOdd(s[i])
}

method checkOddSet(s: seq<int>) returns (b: bool)
  requires isSet(s)
  ensures b <==> isSet(s)
  ensures b <==> isOddSet(s)
{ 
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

// For the following methods specify their behaviour so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
// Marks will be awarded for specifying as much as possible all relevant properties of the output.

/* Adds n to a set s, making sure it remains a set */
method addToSet(s: seq<int>, n: int) returns (b: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
  // Marks will be awarded for specifying as much as possible all relevant properties of the output.
  // Hint: You don't need to reimplement addToSet as a function to use in your specification.
  requires isSet(s)
  ensures |b| >= |s|     // Ensures that b is greater or equal to s
  ensures b[..|s|] == s // Ensures that the prefix of b is s 
  ensures isSet(b)
  ensures exists x: int :: 0 <= x <= |b| && n == b[x]
{ // TODO: Implement the method
  if n !in s {
    b := s + [n];
  } else {
    b := s;
  }
}

/* Unions two sets s1 and s2, returning a new set t */
method union(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
  requires isSet(s1) 
  requires isSet(s2)
  ensures isSet(t)
  ensures forall x :: 0 <= x <= |t| ==> t[x] in s1 || t[x] in s2
{ 
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
  
/* Intersects two sets s1 and s2, returning a new set t */
method intersection(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
requires isSet(s1)
requires isSet(s2) 
ensures isSet(t)
ensures forall x :: 0 <= x < |t| ==> (t[x] in s1 && t[x] in s2)
{ 
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

/* Difference of two sets s1 and s2, returning a new set t = s1 - s2 */
method difference(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
  requires isSet(s1) // Requires s1 to be a set
  requires isSet(s2) // Requires s2 to be a set
  ensures isSet(t)
  ensures forall x :: 0 <= x < |t| ==> (t[x] !in s2 && t[x] in s1)  
{ 
  var i := 0;
  t := [];
  while i < |s1| 
    // invariant 0 <= i <= |s1|
    { 
      if s1[i] !in s2 {  // Don't include anything from s1 that is also in s2.
        t := addToSet(t, s1[i]);
      }
      i := i + 1;
    }
}

/* Multiplies each element of a set s by n, returning a new set t */
method setScale(s: seq<int>, n: int) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
  requires isSet(s)
  ensures forall x:int :: 0 <= x < |t| ==> (t[x] / n) in s   
{ 
  var i := 0; 
  t := [];
  var placeholder := 0;
  while i < |s| 
    invariant 0 <= i <= |s|
    invariant isSet(s)
    decreases |s| - i
    // invariant placeholder !in t
    {
      placeholder := s[i] * n;
      t := addToSet(t, placeholder);
      i := i + 1;
    }
    assert isSet(t); 
}

/* Computes the product set of two sets s1 and s2, returning a new set t = { n * m | n in s1, m in s2 }  */
method setProduct(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
  requires isSet(s1) 
  requires isSet(s2)
  ensures forall x :: 0 <= x < |t| ==> exists y, z :: 0 <= y < |s1| && 0 <= z < |s2| && t[x] == s1[y] * s2[z]    
{ 
  var i := 0; 
  var j := 0;
  t := []; 
  while i < |s1| 
    // invariant 0 <= i <= |s1|
    // decreases |s1| - i 
    // decreases |s2| - i 
    {
      while j < |s2| {
        var placeholder := s1[i] * s2[j];
        t := addToSet(t, placeholder);
        j := j + 1;
      }
      i := i + 1;
    }
  assert isSet(t);
}

/* Converts an even set to an odd set by inverting the parity of each element  
   Hint: Use the invertParity function */
method invertParitySet(s: seq<int>) returns (t:seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
  requires isSet(s) 
  requires isEvenSet(s) 
  ensures isSet(t) 
{  
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
