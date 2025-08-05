export function mvParser(contents) {
  console.log('handling the file with: ' + contents);
  const frontMatterRegex = /^\(\*---\r?\n([\s\S]*?)\r?\n---\*\)/;
  const match = contents.match(frontMatterRegex);

  if (!match) {
    return {};
  }

  const frontMatterBlock = match[1];
  const content = contents.slice(match[0].length);

  const data = {};
  frontMatterBlock.split(/\r?\n/).forEach((line) => {
    const [key, ...valueParts] = line.split(':');
    if (key && valueParts.length) {
      data[key.trim()] = valueParts.join(':').trim();
    }
  });

  if (content.trim()) {
    data.content = content;
  }

  return data;
}
