

x:=0;
y:=0;
z:=0;
havoc a, b, c;

if not a = 0 then {
  x := -2
};

if b < 5 then {
  if a = 0 and not(c = 0) then
    y := 1;
  z := 2
};

assert not x+y+z = 3
