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

method checkOddSet(s: seq<int>) returns (b: bool)
{ 
  b := true; 
  var i := 0;
  var counter := 0; // Counter to determine if any elements are not even (iff)
  while i < |s|
      invariant 0 <= i <= |s|
    {
      if s[i] % 2 == 0 {
        counter := counter + 1;
      } 
      i := i + 1;
    }
    assert i == |s|;

  if counter > 0 {
    b := true; 
  } else {
    b := false; 
  }
}