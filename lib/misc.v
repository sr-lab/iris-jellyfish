From iris.heap_lang Require Import notation.


Definition oloc_to_val (ol: option loc) : val := 
  match ol with
  | None => NONEV
  | Some l => SOMEV #l
  end.
