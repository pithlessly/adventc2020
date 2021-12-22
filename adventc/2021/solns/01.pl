#!/usr/bin/env perl
chomp(@lines = <STDIN>);
$r1 = 0;
$r2 = 0;
for ($i = 0; $i < @lines; $i++) {
    $x = @lines[$i];
    if ($i >= 1 and $x > @lines[$i-1]) { $r1++; }
    if ($i >= 3 and $x > @lines[$i-3]) { $r2++; }
}
print "$r1 $r2";
