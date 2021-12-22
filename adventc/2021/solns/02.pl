#!/usr/bin/env perl

$x = $y1 = $y2 = 0;
while (<>) {
    if (/up (.*)/) { $y1 -= $1 }
    if (/down (.*)/) { $y1 += $1 }
    if (/forward (.*)/) { $x += $1; $y2 += $y1 * $1 }
}
$y1 *= $x; $y2 *= $x;
print "$y1 $y2";
