#let frontmatter = (
    date: datetime(year: 2026, month: 08, day: 26),
    title: "Making Things Typier",
    authors: "Raymond Baker",
)

= Look Ma, no Haskell!

This used to be Slick site. There used to be Haskell here. This used to be a blessed place. But now its all Typst.

= Why Typst

Managing a build in Haskell and managing the content in another language (usually markdown, though you could use typst with a little effort) was annoying and I honestly stopped trying after setting it up. Moreover, using Shake to build my lil' static (world wide) website was, uh, overkill. I saw #link("https://asta.boserup.eu/forest/forester-typst/")[Asta's] post about moving from Forester to all Typst and thought that if Typst can replicate enough of Forster for her, it can certainly replicate my Slick site. In fact, it makes some things quite a lot easier like #emoji.face.flush or

$
    dif omega in Omega^k (RR^n), dif gamma in Omega^k (RR^n), dif omega and dif gamma in Omega^(k+j)
$

Isn't that nice. Well, okay, you could get all that going using Slick (maybe even with Typst as your content). Mainly I'm cutting a lot of overhead using Slick + Shake to build the site and another language to describe the content. Typst also has a surprisingly nice DX for building a static site: `typst watch --format bundle` launches a static HTTP server that reloads on file change. How grand. As an added bonus, a really simple nix flake means its very easy to pick up editing this site anywhere that can clone this git repo. I don't even have to remember the commands for building the site and such, they're all in the nix flake (I really am suffering the worst form of brain rot).

= What happened to the wonderful purple theme you had?

Once I figure out how to include CSS using typst its so over for you

= Why not latex?

I dunno, something about the L3 programming layer just seems... like complicated or something. Like I said, man, I really am suffering the worst form of brain rot.
