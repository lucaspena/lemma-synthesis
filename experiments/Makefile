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
	echo "\nRunning reachability"
	command time -f $(timeformat) python3 reachability.py
	echo "\nRunning reachability2"
	command time -f $(timeformat) python3 reachability2.py
	echo "\nRunning reachability3"
	command time -f $(timeformat) python3 reachability3.py
	echo "\nRunning reachability4"
	command time -f $(timeformat) python3 reachability4.py
	echo "\nRunning reachability5"
	command time -f $(timeformat) python3 reachability5.py
	echo "\nRunning reachability6"
	command time -f $(timeformat) python3 reachability6.py
	echo "\nRunning slseg-lseg"
	command time -f $(timeformat) python3 slseg-lseg.py
	echo "\nRunning lseg-nil-list"
	command time -f $(timeformat) python3 lseg-nil-list.py
#	echo "\nRunning list-find"
#	command time -f $(timeformat) python3 list-find.py
#	echo "\nRunning lseg-list-keys"
#	command time -f $(timeformat) python3 lseg-list-keys.py
#	echo "\nRunning slist-find"
#	time python3 slist-find.py
#	echo "\nRunning slseg-nil_slist"
#	command time -f $(timeformat) python3 slseg-nil-slist.py
#	echo "\nRunning lseg-nil-length"
#	command time -f $(timeformat) python3 lseg-nil-length.py
#	echo "\nRunning lseg-list-length"
#	command time -f $(timeformat) python3 lseg-list-length.py
#	echo "\nRunning bst-tree"
#	command time -f $(timeformat) python3 bst-tree.py
#	echo "\nRunning maxheap-tree"
#	command time -f $(timeformat) python3 maxheap-tree.py
	echo "\nExperiments Done\n"

clean:
	rm -f **/*_KLemmas.txt
	rm -f **/out*.sy
	rm -f **/out*.smt2
