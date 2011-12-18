public proc yorn(prompt:string)
       do  print(prompt)
       	   print(" (y/n) ")
           read_char(response)
	   result = is_yes(response)
	   unless is_yes_or_no(response)
	   println("Please answer 'yes' or 'no'.")
	   until is_yes_or_no(response)
	end
 end
