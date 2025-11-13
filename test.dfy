method FindMax(a: array<int>) returns (i: int)
  requires a != null && a.Length > 0
  ensures 0 <= i < a.Length ==> forall j :: 0 <= j < a.Length ==> a[i] >= a[j]
{
  var maxIndex := 0;
  var j := 1;

  while j < a.Length
    invariant 0 <= maxIndex < a.Length
    invariant 1 <= j <= a.Length
    invariant forall k :: 0 <= k < j ==> a[maxIndex] >= a[k]
  {
    if a[j] > a[maxIndex] {
      maxIndex := j;
    }
    j := j + 1;
  }

  i := maxIndex;
}

method intersection(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.

{ // TODO: Implement the method
  var i := 0; 
  var newvalue := 0;
  while i < |s2| {
    newvalue := newvalue + s2[i];
    i := i + 1;
  }
  t := s1 + [newvalue];
}
/* A set is represented as a sequence with no duplicates */
predicate isSet(s: seq<int>) {
 // TODO: complete this predicate
  forall i, j :: 0 <= i < |s| &&  0 <= j < |s| && i != j ==> s[i] != s[j] 
}


/* Unions two sets s1 and s2, returning a new set t */
method union(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
  requires isSet(s1) 
  requires isSet(s2)
  ensures isSet(t)
{ 
  var i := 0; 
  var j := 0; 
  var counter := 0; 
  t := s1;  // Initialise t to be equal the first set 
  while i < |s2| 
    invariant 0 <= i <= |s2|  // Keep i within the size of 
    invariant isSet(s2[i])
    decreases |s2| - i 
  {
      counter := 0; // Re-initialise the counter on each loop 
      j := 0;       // Re-initialise j on each loop. 
      while j < |s1|
        invariant 0 <= j <= |s1|
        decreases |s1| - j
      {
        if s2[i] == s1[j] {   // if a match exists, update the counter 
          counter := counter + 1; 
        }
        j := j + 1;
      }
      if counter == 0 {
        t := addToSet(t, s2[i]);
      }
      i := i + 1;
    }
}

method addToSet(s: seq<int>, n: int) returns (b: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
  // Marks will be awarded for specifying as much as possible all relevant properties of the output.
  // Hint: You don't need to reimplement addToSet as a function to use in your specification.
  requires isSet(s)
  requires n !in s       // Ensures that n is not already in s 
  ensures |b| >= |s|     // Ensures that b is greater than s
  ensures b[..|s|] == s // Ensures that the prefix of b is s 
  ensures isSet(b)
{ // TODO: Implement the method
    b := s + [n];
}
