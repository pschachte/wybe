public proc yorn(prompt:string)
    do  print(prompt)
	print(" (y/n) ")
	read_line(response)
	responsechar = to_upper(first(response))
	result = responsechar == "Y"
	until result or responsechar == "N"
	println("Please answer 'yes' or 'no'.")
    end
 end
