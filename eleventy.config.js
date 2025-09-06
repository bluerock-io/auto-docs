import YAML from 'yaml';
import { mvParser } from './_11ty/mv-parser.js';
import { parseCoqContent } from './_11ty/coq-parser.js';
import { rocqToMd } from './_11ty/rocq-converter.js';
import slugify from '@sindresorhus/slugify'; /* same as 11ty */
import markdownItDefList from "markdown-it-deflist";
import markdownItContainer from "markdown-it-container";
import brokenLinks from 'eleventy-plugin-broken-links';

import syntaxHighlight from '@11ty/eleventy-plugin-syntaxhighlight';

import { markdownify, unmarkdownify } from './_11ty/filters.js';

export default function (eleventyConfig) {
  eleventyConfig.addPlugin(syntaxHighlight);
  eleventyConfig.addPlugin(brokenLinks);
  eleventyConfig.addDataExtension('yaml', (contents) => {
      return YAML.parse(contents);
  });

  eleventyConfig.addGlobalData('siteTitle', 'BlueRock FM Docs');
  eleventyConfig.addTemplateFormats('v');
  eleventyConfig.addPreprocessor('markdown-rocq', 'v', (data, content) => {
    const sentences = parseCoqContent(content);
    const markdownOutput = rocqToMd(sentences);
    return markdownOutput;
  });
  eleventyConfig.addExtension('v', {
    key: 'md',
  });

  // Markdown Extensions
  eleventyConfig.amendLibrary("md", (mdLib) => {
      mdLib.use(markdownItDefList);
      function container(name, cls) {
          let re = new RegExp(`^${name}$`, '');
          mdLib.use(markdownItContainer, name, {
              validate: function(params) {
                  return params.trim().match(re);
              },

              render: function (tokens, idx) {
                  var m = tokens[idx].info.trim().match(re);

                  if (tokens[idx].nesting === 1) {
                      // opening tag
                      return `<div class="${cls}" role="alert">\n`;
                  } else {
                      // closing tag
                      return '</div>\n';
                  }
              }
          });
      }
      container('info', 'alert alert-info');
      container('success', 'alert alert-success');
      container('warn', 'alert alert-warning');
  });

  // Collections
  eleventyConfig.addCollection('learn', function (collectionApi) {
    return collectionApi.getFilteredByTag('learn');
  });

  eleventyConfig.addCollection('reference', function (collectionApi) {
    return collectionApi.getFilteredByTag('doc');
  });

  eleventyConfig.addCollection('where', function (collectionApi) {
    const allProvides = collectionApi
      .getAll()
      .flatMap((item) => item.data.provides || []);
    return [...new Set(allProvides)];
  });

  eleventyConfig.addFilter('terminology', (value) => {
    // Extend this to add a link to a canonical article if one exists.
    if (false) {
      return `<a href="/where/${slugify(value)}">${value}</a>`;
    } else {
      return value;
    }
  });
    eleventyConfig.addFilter('filename', (value) => {
        return value.slice(value.lastIndexOf('/') + 1);
    });

  eleventyConfig.addFilter('md', markdownify);
  eleventyConfig.addFilter('un_md', unmarkdownify);

  // Passthrough files

  eleventyConfig.addPassthroughCopy({
    'node_modules/lunr/lunr.min.js': 'node_modules/lunr/lunr.min.js',
  });
  eleventyConfig.addPassthroughCopy('content/**/*.v', {
    mode: 'html-relative',
    failOnError: true
  });
  eleventyConfig.addPassthroughCopy('content/assets');

  // eleventyConfig.addExtension("v", {
  //     compile: async (inputContent)  => {
  //         const sentences = parseCoqContent(inputContent);
  //         const markdownOutput = rocqToMd(sentences);
  //         return async () => {
  //             return markdownOutput;
  //         };
  //     }
  // });

  //   eleventyConfig.addCollection("allContentPages", function(collectionApi) {
  //   return collectionApi.getAll().filter(item => {
  //     // Filter out index pages and ensure it's a content file
  //     return item.inputPath.startsWith('./content/') &&
  //            !item.inputPath.includes('index.') &&
  //            (item.inputPath.endsWith('.md') || item.inputPath.endsWith('.html') || item.inputPath.endsWith('.v'));
  //   }).sort((a, b) => a.data.title.localeCompare(b.data.title)); // Sort by title
  // });
}
export const config = {
  dir: {
    input: 'content',
    output: '_site',
    includes: '../_includes',
  },
};
