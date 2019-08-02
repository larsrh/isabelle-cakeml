chapter \<open>Generated by Lem from \<open>list_extra.lem\<close>.\<close>

theory "Lem_list_extra" 

imports
  Main
  "Lem_bool"
  "Lem_maybe"
  "Lem_basic_classes"
  "Lem_tuple"
  "Lem_num"
  "Lem_list"
  "Lem_assert_extra"

begin 



\<comment> \<open>\<open>open import Bool Maybe Basic_classes Tuple Num List Assert_extra\<close>\<close>

\<comment> \<open>\<open> ------------------------- \<close>\<close>
\<comment> \<open>\<open> head of non-empty list    \<close>\<close>
\<comment> \<open>\<open> ------------------------- \<close>\<close>
\<comment> \<open>\<open>val head : forall 'a. list 'a -> 'a\<close>\<close>
\<comment> \<open>\<open>let head l=  match l with | x::xs -> x | [] -> failwith "List_extra.head of empty list" end\<close>\<close>


\<comment> \<open>\<open> ------------------------- \<close>\<close>
\<comment> \<open>\<open> tail of non-empty list    \<close>\<close>
\<comment> \<open>\<open> ------------------------- \<close>\<close>
\<comment> \<open>\<open>val tail : forall 'a. list 'a -> list 'a\<close>\<close>
\<comment> \<open>\<open>let tail l=  match l with | x::xs -> xs | [] -> failwith "List_extra.tail of empty list" end\<close>\<close>


\<comment> \<open>\<open> ------------------------- \<close>\<close>
\<comment> \<open>\<open> last                      \<close>\<close>
\<comment> \<open>\<open> ------------------------- \<close>\<close>
\<comment> \<open>\<open>val last : forall 'a. list 'a -> 'a\<close>\<close>
\<comment> \<open>\<open>let rec last l=  match l with | [x] -> x | x1::x2::xs -> last (x2 :: xs) | [] -> failwith "List_extra.last of empty list" end\<close>\<close>


\<comment> \<open>\<open> ------------------------- \<close>\<close>
\<comment> \<open>\<open> init                      \<close>\<close>
\<comment> \<open>\<open> ------------------------- \<close>\<close>

\<comment> \<open>\<open> All elements of a non-empty list except the last one. \<close>\<close>
\<comment> \<open>\<open>val init : forall 'a. list 'a -> list 'a\<close>\<close>
\<comment> \<open>\<open>let rec init l=  match l with | [x] -> [] | x1::x2::xs -> x1::(init (x2::xs)) | [] -> failwith "List_extra.init of empty list" end\<close>\<close>


\<comment> \<open>\<open> ------------------------- \<close>\<close>
\<comment> \<open>\<open> foldl1 / foldr1           \<close>\<close>
\<comment> \<open>\<open> ------------------------- \<close>\<close>

\<comment> \<open>\<open> folding functions for non-empty lists,
    which don`t take the base case \<close>\<close>
\<comment> \<open>\<open>val foldl1 : forall 'a. ('a -> 'a -> 'a) -> list 'a -> 'a\<close>\<close>
fun foldl1  :: "('a \<Rightarrow> 'a \<Rightarrow> 'a)\<Rightarrow> 'a list \<Rightarrow> 'a "  where 
     " foldl1 f (x # xs) = ( List.foldl f x xs )" 
  for  f  :: " 'a \<Rightarrow> 'a \<Rightarrow> 'a " 
  and  xs  :: " 'a list " 
  and  x  :: " 'a "
|" foldl1 f ([]) = ( failwith (''List_extra.foldl1 of empty list''))" 
  for  f  :: " 'a \<Rightarrow> 'a \<Rightarrow> 'a "


\<comment> \<open>\<open>val foldr1 : forall 'a. ('a -> 'a -> 'a) -> list 'a -> 'a\<close>\<close>
fun foldr1  :: "('a \<Rightarrow> 'a \<Rightarrow> 'a)\<Rightarrow> 'a list \<Rightarrow> 'a "  where 
     " foldr1 f (x # xs) = ( List.foldr f xs x )" 
  for  f  :: " 'a \<Rightarrow> 'a \<Rightarrow> 'a " 
  and  xs  :: " 'a list " 
  and  x  :: " 'a "
|" foldr1 f ([]) = ( failwith (''List_extra.foldr1 of empty list''))" 
  for  f  :: " 'a \<Rightarrow> 'a \<Rightarrow> 'a "


  
\<comment> \<open>\<open> ------------------------- \<close>\<close>
\<comment> \<open>\<open> nth element               \<close>\<close>
\<comment> \<open>\<open> ------------------------- \<close>\<close>

\<comment> \<open>\<open> get the nth element of a list \<close>\<close>
\<comment> \<open>\<open>val nth : forall 'a. list 'a -> nat -> 'a\<close>\<close>
\<comment> \<open>\<open>let nth l n=  match index l n with Just e -> e | Nothing -> failwith "List_extra.nth" end\<close>\<close>


\<comment> \<open>\<open> ------------------------- \<close>\<close>
\<comment> \<open>\<open> Find_non_pure             \<close>\<close>
\<comment> \<open>\<open> ------------------------- \<close>\<close>
\<comment> \<open>\<open>val findNonPure : forall 'a. ('a -> bool) -> list 'a -> 'a\<close>\<close> 
definition findNonPure  :: "('a \<Rightarrow> bool)\<Rightarrow> 'a list \<Rightarrow> 'a "  where 
     " findNonPure P l = ( (case  (List.find P l) of 
    Some e      => e
  | None     => failwith (''List_extra.findNonPure'')
))" 
  for  P  :: " 'a \<Rightarrow> bool " 
  and  l  :: " 'a list "



\<comment> \<open>\<open> ------------------------- \<close>\<close>
\<comment> \<open>\<open> zip same length           \<close>\<close>
\<comment> \<open>\<open> ------------------------- \<close>\<close>

\<comment> \<open>\<open>val zipSameLength : forall 'a 'b. list 'a -> list 'b -> list ('a * 'b)\<close>\<close> 
fun  zipSameLength  :: " 'a list \<Rightarrow> 'b list \<Rightarrow>('a*'b)list "  where 
     " zipSameLength l1 l2 = ( (case  (l1, l2) of
    (x # xs, y # ys) => (x, y) # zipSameLength xs ys
  | ([], []) => []
  | _ => failwith (''List_extra.zipSameLength of different length lists'')

))" 
  for  l1  :: " 'a list " 
  and  l2  :: " 'b list "


\<comment> \<open>\<open>val     unfoldr: forall 'a 'b. ('a -> maybe ('b * 'a)) -> 'a -> list 'b\<close>\<close>
function (sequential,domintros)  unfoldr  :: "('a \<Rightarrow>('b*'a)option)\<Rightarrow> 'a \<Rightarrow> 'b list "  where 
     " unfoldr f x = (
  (case  f x of
      Some (y, x') =>
        y # unfoldr f x'
    | None =>
        []
  ))" 
  for  f  :: " 'a \<Rightarrow>('b*'a)option " 
  and  x  :: " 'a " 
by pat_completeness auto


end
