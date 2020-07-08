all:
	echo "\nRunning dlist-list"
	time python3 dlist-list.py
	echo "\nRunning slist-list"
	time python3 slist-list.py
	echo "\nRunning sdlist-dlist"
	time python3 sdlist-dlist.py
	echo "\nRunning sdlist-dlist-and-slist"
	time python3 sdlist-dlist-and-slist.py
	echo "\nRunning listlen-list"
	time python3 listlen-list.py
	echo "\nRunning lseg-list"
	time python3 lseg-list.py
	echo "\nRunning reachability"
	time python3 reachability.py
	echo "\nRunning slseg-lseg"
	time python3 slseg-lseg.py
	echo "\nRunning lseg-nil-list"
	time python3 lseg-nil-list.py
	echo "\nRunning list-find"
	time python3 list-find.py
	echo "\nRunning lseg-list-keys"
	time python3 lseg-list-keys.py
	echo "\nRunning slist-find"
	time python3 slist-find.py
	echo "\nRunning slseg-nil_slist"
	time python3 slseg-nil-slist.py
	echo "\nRunning lseg-nil-length"
	time python3 lseg-nil-length.py
	echo "\nRunning lseg-nil-length"
	time python3 lseg-list-length.py
	echo "\nExperiments Done\n"

clean:
	rm -f *_KLemmas.txt
	rm -f out*.sy
	rm -f out*.smt2
