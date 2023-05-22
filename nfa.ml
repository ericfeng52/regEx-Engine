open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)

(*This function takes in: NFA, set of initial states, symbol
  The output will be: set of states in list form that the NFA might be in
  after making one transition on the symbol/epsilon starting from any of the initial states
  Basically, return the list of where we will be after one transition, empty if none*)
    let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
      (*This helper function compares the starting and transitions for each starting state of the list*)
      let move_helper (current_start : 'q) : 'q list =
        List.fold_left (fun transition_list (start, transition, ending) ->
            (*Check if the starting and transition exist within the nfa, if yes, push the end state into list*)
            if current_start = start && transition = s then insert ending transition_list else transition_list) [] nfa.delta
      in
      (*Fold to iterate through the starting states of qs*)
      List.fold_left (fun starting_states state -> insert_all(move_helper state) starting_states) [] qs
    ;;


    let e_closure (nfa : ('q, 's) nfa_t) (qs : 'q list) : 'q list =
      let rec e_helper (r : 'q list) =
        let r_prime = insert_all (move nfa r None) r in
        if eq r r_prime then r else e_helper r_prime
      in
      e_helper qs
    ;;
    


    let rec e_closure_helper (nfa: ('q,'s) nfa_t) (qs: 'q list) (final_list: 'q list): 'q list = match qs with
    | [] -> final_list
    (*If the head isn't already in the final list, then we call move on the head with None and add head to the final state*)
    | h::t -> if(elem h final_list) = false then e_closure_helper nfa (insert_all t (move nfa [h] None)) (h::final_list)
      else e_closure_helper nfa t final_list;;
    (*for the param qs call move and cons it*) (*assign recall onto to call using let and in*)
    (*Match head with the NFA to check if there is eclosure*)
    (*Match with the list, if there is an e_closure existing, put the original state into the new list.*)
    (*Put the final state (where we're at after the epsilon transition) into the original list*)
    (*The original list is going to get recursively called as t is what is left of qs*)
  
  let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list = e_closure_helper nfa qs [];;
    
  let rec accept_helper (nfa: ('q,char) nfa_t) transitions (state_list: 'q list) : 'q list = 
    match transitions with
    |[] -> state_list
    |h::t -> accept_helper nfa t (e_closure nfa (move nfa state_list (Some h)));;
    
    let accept (nfa: ('q,char) nfa_t) (s: string) : bool =
      let bool = fold_left(fun state_list ele -> 
        if elem ele nfa.fs then state_list + 1 else state_list) 0 (accept_helper nfa (explode s) [nfa.q0]) 
      in if bool = 1 then true else false;;
  
(*******************************)
(* Part 2: Subset Construction *)
(*******************************)

let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  List.map (e_closure nfa) (List.map (fun transition -> move nfa qs (Some transition)) nfa.sigma)
;;

let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list =
  List.map (fun transition -> qs, Some transition, e_closure nfa (move nfa qs (Some transition))) nfa.sigma
;;


let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  if intersection qs nfa.fs = [] then [] else [qs]
;;

let rec nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t) (work: 'q list list) : ('q list, 's) nfa_t =
    match work with
    | [] -> dfa
    | h::t ->
      let helper = { sigma = dfa.sigma; 
      qs = insert_all (new_states nfa h) dfa.qs;
      q0 = dfa.q0;
      fs = insert_all (new_finals nfa h) dfa.fs;
      delta = insert_all (new_trans nfa h) dfa.delta }
      in
      nfa_to_dfa_step nfa helper (insert_all (minus helper.qs dfa.qs) t)
  ;;
  

let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t =
  let helper = { sigma = nfa.sigma;
  qs = [e_closure nfa [nfa.q0]];
  q0 = e_closure nfa [nfa.q0];
  fs = [];
  delta = []}
  in
  nfa_to_dfa_step nfa helper helper.qs
;;