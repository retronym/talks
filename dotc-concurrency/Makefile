index.html: talk.md template.html build.py frames.json excerpts.gen.json before.json throughput.json
	python3 build.py

watch:
	@while true; do $(MAKE) -s index.html; sleep 1; done

.PHONY: watch

# needs a checkout of the compiler (SCALA3); not part of the default build, which uses the committed excerpts.gen.json
excerpts:
	python3 extract.py

check:
	python3 extract.py --check

.PHONY: check excerpts
