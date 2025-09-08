import YAML from 'yaml';
import spawn from "node:child_process";
import { mvParser } from './_11ty/mv-parser.js';
import { parseCoqContent } from './_11ty/coq-parser.js';
import { rocqToMd } from './_11ty/rocq-converter.js';
import relativeLinks from "./_11ty/relative-links.js";

import slugify from '@sindresorhus/slugify'; /* same as 11ty */
import markdownItDefList from "markdown-it-deflist";
import markdownItContainer from "markdown-it-container";
import markdownItFootnote from "markdown-it-footnote";
import brokenLinks from 'eleventy-plugin-broken-links';

import syntaxHighlight from '@11ty/eleventy-plugin-syntaxhighlight';
import { InputPathToUrlTransformPlugin } from "@11ty/eleventy";

import { markdownify, unmarkdownify } from './_11ty/filters.js';

export default function (eleventyConfig) {
  eleventyConfig.addPlugin(syntaxHighlight);
  eleventyConfig.addPlugin(brokenLinks);
  eleventyConfig.addDataExtension('yaml', (contents) => {
      return YAML.parse(contents);
  });

  eleventyConfig.addGlobalData('siteTitle', 'BlueRock FM Docs');
  eleventyConfig.addGlobalData("docsTarBall", { path : 'docs', filename : "docs.tar.gz"});
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
      mdLib.use(markdownItFootnote);
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
    return value.slice(value.lastIndexOf('/')+1);
  });

  eleventyConfig.addFilter('md', markdownify);
  eleventyConfig.addFilter('un_md', unmarkdownify);

  // Passthrough files

  eleventyConfig.addPassthroughCopy({
    'node_modules/lunr/lunr.min.js': 'node_modules/lunr/lunr.min.js',
  });
  eleventyConfig.addPassthroughCopy('content/**/*.v', {
    // mode: 'html-relative',
    failOnError: true
  });
  eleventyConfig.addPassthroughCopy('content/assets');
  eleventyConfig.addPassthroughCopy(
    'content/'+eleventyConfig.globalData.docsTarBall.path+'/'+eleventyConfig.globalData.docsTarBall.filename,
    { failOnError: true }
  );


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

  // automatically convert paths to input files to output files
  eleventyConfig.addPlugin(InputPathToUrlTransformPlugin);
  // make all links relative
  eleventyConfig.addPlugin(relativeLinks);

  eleventyConfig.on("eleventy.before", async ({ directories, runMode, outputMode }) => {
		// Run me before the build starts
    // We avoid making the tarball if we are running with watch,
    // as that can cause build with watch to loop.
    if (!runMode.match("build")) return;
    // find ./ -name "*.v" -exec tar -czf docs.tar.gz {} +
    const ls = spawn.spawn(
      'find', ['./','-name','*.v','-exec','tar','-czvf',eleventyConfig.globalData.docsTarBall.filename,'{}','+'],
      { cwd : './content/'+eleventyConfig.globalData.docsTarBall.path, stdio : 'ignore'}
    );

    ls.on('close', (code) => {
      console.log(`Child process creating ${eleventyConfig.globalData.docsTarBall.filename} exited with code ${code}`);
    });
	});
}
export const config = {
  dir: {
    input: 'content',
    output: '_site',
    includes: '../_includes',
  },
};
