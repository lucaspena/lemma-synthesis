timeformat = "real: %e seconds,\tuser: %U seconds,\tsys: %S seconds"

all:
	echo "\nRunning dlist-list"
	command time -f $(timeformat) python3 dlist-list.py
	echo "\nRunning quicksort-nil"
	command time -f $(timeformat) python3 quicksort-nil.py
	echo "\nRunning slist-list"
	command time -f $(timeformat) python3 slist-list.py
	echo "\nRunning sdlist-dlist"
	command time -f $(timeformat) python3 sdlist-dlist.py
	echo "\nRunning sdlist-dlist-and-slist"
	command time -f $(timeformat) python3 sdlist-dlist-and-slist.py
	echo "\nRunning listlen-list"
	command time -f $(timeformat) python3 listlen-list.py
	echo "\nRunning lseg-list"
	command time -f $(timeformat) python3 lseg-list.py
# 	echo "\nRunning reachability"
# 	time python3 reachability.py
# 	echo "\nRunning reachability2"
# 	time python3 reachability2.py
# 	echo "\nRunning reachability3"
# 	time python3 reachability3.py
# 	echo "\nRunning reachability4"
# 	time python3 reachability4.py
# 	echo "\nRunning reachability5"
# 	time python3 reachability5.py
# 	echo "\nRunning reachability6"
# 	time python3 reachability6.py
# 	echo "\nRunning slseg-lseg"
# 	time python3 slseg-lseg.py
# 	echo "\nRunning lseg-nil-list"
# 	time python3 lseg-nil-list.py
# 	echo "\nRunning list-find"
# 	time python3 list-find.py
# 	echo "\nRunning lseg-list-keys"
# 	time python3 lseg-list-keys.py
# 	echo "\nRunning slist-find"
# 	time python3 slist-find.py
# 	echo "\nRunning slseg-nil_slist"
# 	time python3 slseg-nil-slist.py
# 	echo "\nRunning lseg-nil-length"
# 	time python3 lseg-nil-length.py
# 	echo "\nRunning lseg-list-length"
# 	time python3 lseg-list-length.py
# 	echo "\nRunning bst-tree"
# 	time python3 bst-tree.py
# 	echo "\nRunning maxheap-tree"
# 	time python3 maxheap-tree.py
	echo "\nExperiments Done\n"

clean:
	rm -f **/*_KLemmas.txt
	rm -f **/out*.sy
	rm -f **/out*.smt2
