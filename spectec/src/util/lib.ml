module List =
struct
  include List

  let rec take n xs =
    match n, xs with
    | 0, _ -> []
    | n, x::xs' when n > 0 -> x :: take (n - 1) xs'
    | _ -> failwith "take"

  let rec drop n xs =
    match n, xs with
    | 0, _ -> xs
    | n, _::xs' when n > 0 -> drop (n - 1) xs'
    | _ -> failwith "drop"

  let rec split n xs =
    match n, xs with
    | 0, _ -> [], xs
    | n, x::xs' when n > 0 ->
      let xs1', xs2' = split (n - 1) xs' in x::xs1', xs2'
    | _ -> failwith "split"

  let split_hd = function
    | x::xs -> x, xs
    | _ -> failwith "split_hd"

  let rec split_last_opt' ys = function
    | x::[] -> Some (List.rev ys, x)
    | x::xs -> split_last_opt' (x::ys) xs
    | [] -> None
  let split_last_opt xs = split_last_opt' [] xs
  let split_last l = Option.get (split_last_opt l)

  let last_opt l = Option.map snd (split_last_opt l)
  let last l = snd (split_last l)

  let rec nub pred = function
    | [] -> []
    | x::xs -> x :: nub pred (List.filter (fun y -> not (pred x y)) xs)

  let filter_not pred = List.filter (fun x -> not (pred x))
end

module Char =
struct
  let is_digit_ascii c = '0' <= c && c <= '9'
  let is_uppercase_ascii c = 'A' <= c && c <= 'Z'
  let is_lowercase_ascii c = 'a' <= c && c <= 'z'
  let is_letter_ascii c = is_uppercase_ascii c || is_lowercase_ascii c
end

module String =
struct
  include String

  let implode cs =
    let buf = Buffer.create 80 in
    List.iter (Buffer.add_char buf) cs;
    Buffer.contents buf

  let explode s =
    let cs = ref [] in
    for i = String.length s - 1 downto 0 do cs := s.[i] :: !cs done;
    !cs

  let unquote s = 
    let len = String.length s in
    let l = if s.[0] = '"' then 1 else 0 in
    let r = if s.[len - 1] = '"' then len - 1 else len in
    String.sub s l (r - l)

  let replace p t s =
    let len = String.length p in
    if len = 0 then s else
    let rec aux i acc =
      if i > String.length s - len then
        acc ^ String.sub s i (String.length s - i)
      else if String.sub s i len = p then
        aux (i + len) (acc ^ t)
      else
        aux (i + 1) (acc ^ String.make 1 s.[i])
    in
    aux 0 ""
end
