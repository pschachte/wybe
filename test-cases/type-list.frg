public type list(t) =
	[]
	[|](head:t, tail:list(t))
end

public func ++(x:list(t), y:list(t)) =
    if x == []
    then y
    else [head(x)|tail(x)++y]
