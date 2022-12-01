divert(-1)
  This program reveals an annoying behavior, for my purposes, of
  GNU m4: it assumes that it's dealing with C strings and doesn't
  think of NUL bytes in too many places. I don't think it makes
  this assumption within the obstack itself, but I can't create
  NUL bytes through the %c format directive because the resulting
  string is treated as empty. See lines 360 and 391:
  
https://git.savannah.gnu.org/gitweb/?p=m4.git;a=blob;f=src/format.c;h=40a10ebf548ce4f302829e36f0618d6d79322c82;hb=refs/heads/branch-1.4#l360
  
  Inspecting the output of this program, you'll notice that the
  other unprintable bytes are all emitted correctly except NUL.
divert(0)dnl
define(`byte',`format(`%c',`$1')`'')dnl
byte(72)byte(105)byte(129)byte(1)byte(0)byte(1)byte(10)dnl
