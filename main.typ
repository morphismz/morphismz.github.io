#set document(format: "html")

#let pages = ("posts/making-things-typier","jokes", "faqs")
#let sites = (:)

#for f in pages {
    import path( "/site/" + f + ".typ") as site
    let fm = site.frontmatter
    let name = f.split("/").last()
    fm.insert("name", name)
    sites.insert(f, ( frontmatter: fm, content: site ))
}

#let makePage(doc) = [
    #let (here, site) = doc
    #let path = here + ".html"

    #document(
        path,
        title: site.frontmatter.title,
    )[
        #title()

        #let container = label("container:" + site.frontmatter.name)
        #html.section[
            #site.content
        ] #container
        #outline(target: heading.where().within(container))
    ] #label(site.frontmatter.name)
]

#let makePages(docs) = {
    for doc in docs {
        makePage(doc)
    }
}

#let index = {
    let f = "index"
    import path( "/site/" + f + ".typ") as site
    let fm = site.frontmatter
    fm.insert("name", "index")
    (f, ( frontmatter: fm, content: site ))
}

#let frontPage = {
    makePage(index)
}

#frontPage

#makePages(sites)
