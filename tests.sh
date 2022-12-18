find tests -name main.n | xargs -rI '{}' 'sh' -c 'echo -n "{}: " && zig-out/bin/bootstrap {} >/dev/null 2>&1 || exit 1 && ./a.out || exit 1'
