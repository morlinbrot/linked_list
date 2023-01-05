default:
	just -l -u

alias mi := miri
miri *PARAMS:
	cargo +nightly watch -x "miri test {{PARAMS}}"

alias t := test
test *PARAMS:
	cargo test {{PARAMS}}

watch *PARAMS:
	cargo watch -s "just test {{PARAMS}}"

alias c := clip
clip *PARAMS:
	cargo watch -x "clippy {{PARAMS}}"
