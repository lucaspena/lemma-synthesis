all:
	time python3 alldone_dlist-list.py
	time python3 alldone_slist-list.py
	time python3 alldone_sdlist-dlist.py
	time python3 alldone_sdlist-dlist-and-slist.py
	time python3 alldone_listlen-list.py
	time python3 alldone_lseg-list.py
	time python3 alldone_reachability.py
	time python3 alldone_slseg-lseg.py
	echo "\nExperiments Done\n"
	# Problematic example -- valid lemma proposed again and again
	#time python3 list-find.py
	#time python3 slist-find.py
	#time python3 lseg-nil-list.py
	#time python3 lseg-list-keys.py
	#time python3 slseg-nil-list.py
	#time python3 lseg-nil-length.py
	#time python3 lseg-list-length.py

clean:
	rm -f *_KLemmas.txt
	rm -f out*.sy
	rm -f out*.smt2
