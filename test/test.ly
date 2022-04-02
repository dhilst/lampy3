def fact x : forall, int -> int =
    if x == 0
    then 1
    else x * fact (x - 1);;


def test () : forall, unit -> unit =
    assert (fact 5 == 120);
    ();;
