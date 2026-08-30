#let frontmatter = (
    date: datetime(year: 2026, month: 08, day: 26),
    title: "Raymond Baker's Personal (World Wide) Website",
    authors: "Raymond Baker",
)

#let makeLinks(pages) = {
    for f in pages [
    #import path( "/site/" + f + ".typ") as site
    #let fm = site.frontmatter
    #let name = f.split("/").last()
    - #link(f + ".html")[#site.frontmatter.title]
    ]
}

= Intro

My name is Raymond Baker. I am currently working as software engineer at Mercury, hacking on their payments infrastructure in Haskell. Previously I worked as a Haskell programmer at MasterWord Services. And before that I worked as a high school math teacher at Temple Grandin School, a small school serving students on autism the spectrum. And before that I studied mathematics and philosophy at CU Boulder. I graduated in 2023 with with the honors _summa cum laude_. And before that I spent a number of years as a child.

= Posts

#let posts = ("posts/making-things-typier",)

#makeLinks(posts)

= Misc

#let misc = ("faqs", "jokes")

#makeLinks(misc)
