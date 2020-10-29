in_handle = open('out.smt2', 'r')
out_handle = open('annotated_out.smt2','w')

in_str = in_handle.read()
in_lines = in_str.split('\n')

for in_line in in_lines:
  if 'assert' in in_line:
    line_split = in_line[:-2].split('(')
    name =  '_'.join([entity for elem in line_split[2:] for entity in elem.split(' ')])
    name = 'name_' + ''.join(name.split(')'))[3:]
    out_line = '(' + line_split[1] + '(! (' + '('.join(line_split[2:]) + ') :named ' + name + '))\n'
  else:
    out_line = in_line + '\n'
  out_handle.write(out_line)

