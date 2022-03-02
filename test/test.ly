fun not_ x =
    if x
    then false
    else true
end


print (not_ false)


fun fact x =
    if x == 0
    then 1
    else x * fact (x - 1)
end

print (fact 5)
