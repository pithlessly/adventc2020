fun sum_loop
  {l:addr}{n:nat}
  (arr: array_v(int, l, n) | p: ptr l, len: int n, acc: int):
    (array_v(int, l, n) | int) =
  if (len = 0) then
    (arr | acc)
  else
    let
      prval (head, tail) = array_v_uncons(arr)
      val (tail | i) = sum_loop(tail | _, len - 1, acc + !p)
    in
      (array_v_cons(head, tail) | i)
    end

fn sum
  {l:addr}{n:nat}
  (arr: array_v(int, l, n) | p: ptr l, len: int n):
    (array_v(int, l, n) | int) =
  sum_loop(arr | p, len, 0)
